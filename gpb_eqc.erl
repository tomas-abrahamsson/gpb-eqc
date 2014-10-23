%%% File    : gpb_eqc.erl
%%% Author  : Thomas Arts <thomas.arts@quviq.com>
%%% Further developed by: Tomas Abrahamsson <tab@lysator.liu.se>
%%% Description : Testing protocol buffer implemented by Tomas Abrahamsson
%%% Created : 12 May 2010 by Thomas Arts

-module(gpb_eqc).

-include_lib("eqc/include/eqc.hrl").
-include("gpb.hrl").

-compile(export_all).

%% Eunit integration
qc_prop_test_() ->
    AllProps = [Fn || {Fn,Arity} <- ?MODULE:module_info(exports),
                      is_property(atom_to_list(Fn), Arity)],
    {Descr, PropsToTest} =
        case os:find_executable("protoc") of
            false ->
                {"QuickCheck tests"
                 " (note: 'protoc' not in $PATH, so excluding some properties)",
                 AllProps -- [prop_encode_decode_via_protoc]};
            P when is_list(P) ->
                {"QuickCheck tests", AllProps}
        end,
    {Descr,
     {timeout, 600,  %% timeout for all tests
      [{timeout, 300, %% timeout for each test
        [{atom_to_list(Prop),
          fun() -> true = eqc:quickcheck(?MODULE:Prop()) end}]}
       || Prop <- PropsToTest]}}.

is_property("prop_"++_, 0) -> true;
is_property(_, _)          -> false.


message_defs() ->
    %% Can we have messages that refer to themselves?
    %% Actually not if field is required, since then we cannot generate
    %% a message of that kind.
    %% left_of/1 guarantees that the messages only refer to earlier definitions
    %% Enums are globally unique. Hence, we generate them globally
    ?LET(MsgNames,eqc_gen:non_empty(ulist("m")),
         ?LET(EnumDefs,enums(),
              begin
                  shuffle(EnumDefs ++
                          [ {{msg,Msg},message_fields(
                                         left_of(Msg,MsgNames),
                                         [ EName || {{enum,EName},_}<-EnumDefs])}
                            || Msg<-MsgNames])
              end)).

%% Take all values left of a certain value
left_of(X,Xs) ->
    lists:takewhile(fun(Y) ->
                            Y/=X
                    end,Xs).

message_fields(MsgNames, EnumNames) ->
    %% can we have definitions without any field?
    ?LET({FieldDefs, FNumBase0},
         {eqc_gen:non_empty(
            list({elements([{required, msg_field_type(MsgNames, EnumNames)},
                            {optional, msg_field_type(MsgNames, EnumNames)},
                            {repeated, msg_field_type(MsgNames, EnumNames)},
                            {oneof,    oneof_fields(MsgNames, EnumNames)}]),
                  field_name()})),
          uint(10)},
         mk_fields(FieldDefs, FNumBase0+1)).

message_name() ->
    elements([m1,m2,m3,m4,m5,m6]).

field_name() ->
    elements([a,b,c,field1,f]).

oneof_fields(MsgNames, EnumNames) ->
    ?LET({FieldDefs, FNumBase0},
         {eqc_gen:non_empty(
            list({elements([{optional, msg_field_type(MsgNames, EnumNames)}]),
                  field_name()})),
          uint(10)},
         mk_fields(FieldDefs, FNumBase0+1)).

msg_field_type([], []) ->
    elements(basic_msg_field_types());
msg_field_type([], EnumNames) ->
    ?LET(EnumName,elements(EnumNames),
         elements(basic_msg_field_types() ++ [{enum, EnumName}]));
msg_field_type(MsgNames, []) ->
    ?LET(MsgName,elements(MsgNames),
         elements(basic_msg_field_types() ++ [{'msg',MsgName}]));
msg_field_type(MsgNames, EnumNames) ->
    ?LET({MsgName, EnumName}, {elements(MsgNames), elements(EnumNames)},
         elements(basic_msg_field_types() ++
                  [{enum, EnumName}, {'msg',MsgName}])).

basic_msg_field_types() ->
    [bool,sint32,sint64,int32,int64,uint32,
     uint64,
     fixed64,sfixed64,double,
     fixed32,
     sfixed32,
     float,
     bytes,
     string
    ].

mk_fields(FieldDefs, FNumBase) ->
    UFieldDefs = keyunique(2, FieldDefs),
    {Fields, _NextFNum} =
        lists:mapfoldl(
          fun({{{required, Type}, FieldName}, RNum}, FNum) ->
                  {#?gpb_field{name=FieldName, fnum=FNum, rnum=RNum,
                               type=Type, occurrence=required, opts=[]},
                   FNum+1};
             ({{{optional, Type}, FieldName}, RNum}, FNum) ->
                  {#?gpb_field{name=FieldName, fnum=FNum, rnum=RNum,
                               type=Type, occurrence=optional, opts=[]},
                   FNum+1};
             ({{{repeated, Type}, FieldName}, RNum}, FNum) ->
                  Opts = case Type of
                             {msg,_} -> []; %% FIXME: why not packed?
                             string  -> []; %% FIXME: why not packed?
                             bytes   -> []; %% FIXME: why not packed?
                             _       -> elements([[], [packed]])
                         end,
                  {#?gpb_field{name=FieldName, fnum=FNum, rnum=RNum,
                               type=Type, occurrence=repeated, opts=Opts},
                   FNum+1};
             ({{{oneof, OFields}, FieldName}, RNum}, FNum) ->
                  %% Oneof fields, must have unique names and field numbers
                  %% (within the message)
                  {OFields2, NewFNum} =
                      lists:mapfoldl(
                        fun(#?gpb_field{name=ONm}=F, OFNum) ->
                                OFieldName = combine_name(FieldName, ONm),
                                {F#?gpb_field{name=OFieldName,
                                              rnum=RNum, fnum=OFNum},
                                 OFNum+1}
                        end,
                        FNum,
                        OFields),
                  {#gpb_oneof{name=FieldName, rnum=RNum, fields=OFields2},
                   NewFNum}
          end,
          FNumBase,
          seq_index(UFieldDefs, 2)),
    Fields.

keyunique(_N, []) ->
    [];
keyunique(N, [Tuple|Rest]) ->
    [Tuple| keyunique(N, [ T2 || T2<-Rest, element(N,T2)/=element(N,Tuple)])].

seq_index(L, Start) ->
    lists:zip(L, lists:seq(1+(Start-1),length(L)+(Start-1))).

combine_name(NameA, NameB) ->
    list_to_atom(lists:concat([NameA, "_", NameB])).

%% In fact, we should improve this to have different enums containing same value
%% e.g. [ {{enum,e1},[{x1,10}]}, {{enum,x2},[{x2,10}]} ]
enums() ->
    ?LET({N,Values,Names},{int(),ulist("x"),ulist("e")},
         ?LET(Constants,unique_values(Values,N),
              enums(Names,Constants))).

ulist(String) ->
    ?LET(N,nat(),
         [ list_to_atom(String++integer_to_list(K)) || K<-lists:seq(1,N) ]).

%% Unique names and unqiue values
%% Example
%% enum file_open_return_values { enoent=1, eacess=2 }
unique_values([],_N) ->
    [];
unique_values([Cons|Conss],N) ->
    ?LET(Next,nat(),
         [{Cons,N} | unique_values(Conss,Next+N+1)]).

enums([],_Conss) ->
    [];
enums(_Enames,[]) ->
    [];
enums([Ename|Enames],Conss) ->
    ?LET(Element,elements(Conss),
         begin
             Prefix = left_of(Element,Conss)++[Element],
             [{{enum,Ename},Prefix}|enums(Enames,Conss--Prefix)]
         end).


%% generator for messages that respect message definitions

message(MessageDefs) ->
    MsgDefs = [MD || {{msg,_MsgName},_}=MD <- MessageDefs], % filter out enums
    ?LET({{msg,Msg},_Fields},oneof(MsgDefs),
         message(Msg,MessageDefs)).

message(Msg,MessageDefs) ->
    Fields = proplists:get_value({msg,Msg},MessageDefs),
    FieldValues = [case Field of
                       #?gpb_field{} -> field_value(Field, MessageDefs);
                       #gpb_oneof{}  -> oneof_value(Field, MessageDefs)
                   end
                   || Field <- Fields],
    list_to_tuple([Msg|FieldValues]).

oneof_value(#gpb_oneof{fields=OFields}, MessageDefs) ->
    ?LET(OField, oneof(OFields),
         begin
             #?gpb_field{name=Name} = OField,
             oneof([undefined,
                    {Name, field_value(OField#?gpb_field{occurrence=required},
                                       MessageDefs)}])
         end).

field_value(#?gpb_field{type=Type, occurrence=Occurrence}, MsgDefs) ->
    field_val2(Type, Occurrence, MsgDefs).

field_val2(Type, optional, MsgDefs) -> default(undefined, value(Type,MsgDefs));
field_val2(Type, repeated, MsgDefs) -> list(value(Type, MsgDefs));
field_val2(Type, required, MsgDefs) -> value(Type,MsgDefs).

value({msg,M},MessageDefs) ->
    message(M,MessageDefs);
value({enum,E},MessageDefs) ->
    {value, {{enum,E},EnumValues}} = lists:keysearch({enum,E}, 1, MessageDefs),
    ?LET({Symbolic, _ActualValue}, elements(EnumValues),
         Symbolic);
value(bool,_) ->
    bool();
value(sint32,_) ->
    sint(32);
value(sint64,_) ->
    sint(64);
value(int32,_) ->
    int(32);
value(int64,_) ->
    int(64);
value(uint32,_) ->
    uint(32);
value(uint64,_) ->
    uint(64);
value(fixed64,_) ->
    uint(64);
value(sfixed64,_) ->
    sint(64);
value(fixed32,_) ->
    uint(32);
value(sfixed32,_) ->
    sint(32);
value(double, _) ->
    real();
value(float, _) ->
    real();
value(bytes, _) ->
    binary();
value(string, _) ->
    list(encodable_unicode_code_point()).

encodable_unicode_code_point() ->
    %% http://www.unicode.org/versions/Unicode6.0.0/ch03.pdf
    %% * Section 3.3, D9: Code points: integers in the range 0..10ffff
    %% * Section 3.9: The Unicode Standard supports three character
    %%   encoding forms: UTF-32, UTF-16, and UTF-8. Each encoding form
    %%   maps the Unicode code points U+0000..U+D7FF and
    %%   U+E000..U+10FFFF to unique code unit sequences
    ?SUCHTHAT(CP, oneof([uint(16), choose(16#10000, 16#10FFFF)]),
              (0 =< CP andalso CP =< 16#d7ff)
              orelse
                (16#e000 =< CP andalso CP =< 16#10ffff)).

sint(Base) ->
    int(Base).

int(Base) ->
    ?LET(I,uint(Base),
         begin
             << N:Base/signed >> = <<I:Base>>, N
         end).

uint(Base) ->
    oneof([ choose(0,pow2(B)-1) || B<-lists:seq(1,Base)]).

pow2(0)            -> 1;
pow2(N) when N > 0 -> 2*pow2(N-1);
pow2(N) when N < 0 -> 1/pow2(-N).

%%% properties

prop_encode_decode() ->
    Mod = gpb_eqc_m,
    ?FORALL(MsgDefs,message_defs(),
            ?FORALL({Msg, {Encoder, Decoder, COpts}},
                    {message(MsgDefs), encoder_decoder(Mod)},
                    begin
                        MsgName = element(1, Msg),
                        install_msg_defs(Mod, MsgDefs, Encoder, Decoder, COpts),
                        Bin = encode_msg(Msg, MsgDefs, Encoder),
                        DecodedMsg = decode_msg(Bin, MsgName, MsgDefs, Decoder),
                        ?WHENFAIL(io:format("~p /= ~p\n",[Msg, DecodedMsg]),
                                  msg_approximately_equals(Msg, DecodedMsg))
                    end)).

%% add a round-trip via the `protoc' program in the protobuf package.
%% The `protoc' is the compiler generates code from a .proto file, but
%% it can also decode and encode messages on the fly, given a .proto
%% file, so we can use it as an sort of interop test.
prop_encode_decode_via_protoc() ->
    Mod = gpb_eqc_m,
    ?FORALL(MsgDefs,message_defs(),
            ?FORALL({Msg, {Encoder, Decoder, COpts}},
                    {message(MsgDefs), encoder_decoder(Mod)},
                    begin
                        MsgName = element(1, Msg),
                        install_msg_defs(Mod, MsgDefs, Encoder, Decoder, COpts),
                        TmpDir = get_create_tmpdir(),
                        install_msg_defs_as_proto(MsgDefs, TmpDir),
                        GpbBin = encode_msg(Msg, MsgDefs, Encoder),
                        ProtoBin = decode_then_reencode_via_protoc(
                                     GpbBin, Msg, TmpDir),
                        DecodedMsg =
                            decode_msg(ProtoBin, MsgName, MsgDefs, Decoder),
                        ?WHENFAIL(io:format("~p /= ~p\n",[Msg,DecodedMsg]),
                                  msg_approximately_equals(Msg, DecodedMsg))


                    end)).

%% test that we can ignore unknown fields
prop_encode_decode_with_skip() ->
    Mod1 = gpb_eqc_m1,
    Mod2 = gpb_eqc_m2,
    ?FORALL(
       MsgDefs, message_defs(),
       ?FORALL(
          InitialMsg, message(MsgDefs),
          ?FORALL(
             {{SubMsg, SubDefs},
              {Encoder1, Decoder1, COpts1},
              {Encoder2, Decoder2, COpts2}},
             {message_subset_defs(InitialMsg, MsgDefs),
              encoder_decoder(Mod1),
              encoder_decoder(Mod2)},
             begin
                 MsgName = element(1, InitialMsg),
                 install_msg_defs(Mod1, MsgDefs, Encoder1, Decoder1, COpts1),
                 install_msg_defs(Mod2, SubDefs, Encoder2, Decoder2, COpts2),
                 Encoded = encode_msg(InitialMsg, MsgDefs, Encoder1),
                 %% now decode the byte sequence with a decoder that knows
                 %% only a subset of the fields for each message.
                 Decoded = decode_msg(Encoded, MsgName,  SubDefs, Decoder2),
                 ?WHENFAIL(io:format("~p /= ~p\n",[SubMsg, Decoded]),
                           msg_approximately_equals(SubMsg, Decoded))
             end))).

%% test merging of messages
prop_merge() ->
    Mod = gpb_eqc_m,
    ?FORALL(MsgDefs,message_defs(),
        ?FORALL(MsgName, oneof([ M || {{msg,M},_}<-MsgDefs]),
            ?FORALL({Msg1, Msg2, {Encoder, Decoder, COpts}},
                    {message(MsgName,MsgDefs), message(MsgName,MsgDefs),
                     encoder_decoder(Mod)},
                    begin
                        install_msg_defs(Mod, MsgDefs, Encoder, Decoder, COpts),
                        MergedMsg =
                            merge_msgs(Msg1, Msg2, MsgDefs, Encoder, Decoder),
                        Bin1 = encode_msg(Msg1, MsgDefs, Encoder),
                        Bin2 = encode_msg(Msg2, MsgDefs, Encoder),
                        MergedBin = <<Bin1/binary,Bin2/binary>>,
                        DecodedMerge =
                            decode_msg(MergedBin, MsgName, MsgDefs, Decoder),
                        msg_equals(MergedMsg, DecodedMerge)
                    end))).

%% compute a subset of the fields, and also a subset of the msg,
%% corresponding to the subset of the fields.
%% Return {SubsetMsg, SubsetDefs}
message_subset_defs(Msg, MsgDefs) ->
    ?LET(DefsWithSkips,
         [case Elem of
              {{enum,_}, _}=Enum ->
                  Enum;
              {{msg,MsgName}, MsgFields} ->
                  {{msg, MsgName}, msg_fields_subset_skips(MsgFields)}
          end
          || Elem <- MsgDefs],
         begin
             SubsetMsg  = remove_fields_by_skips(Msg, DefsWithSkips),
             SubsetDefs = remove_skips_from_defs(DefsWithSkips),
             {SubsetMsg, SubsetDefs}
         end).

msg_fields_subset_skips(Fields) when length(Fields) == 1 ->
    %% can't remove anything if there's only one field
    ?LET(_, int(),
         Fields);
msg_fields_subset_skips(Fields) ->
    ?LET(Fields2, [elements([Field, skip]) || Field <- Fields],
         %% compensate for removed fields
         Fields2).

remove_fields_by_skips(Msg, DefsWithSkips) ->
    MsgName = element(1, Msg),
    {{msg,MsgName}, MsgDef} = lists:keyfind({msg,MsgName}, 1, DefsWithSkips),
    Fields = [case Field of
                  #?gpb_field{type={msg, _SubMsgName}, occurrence=repeated} ->
                      [remove_fields_by_skips(Elem, DefsWithSkips)
                       || Elem <- Value];
                  #?gpb_field{type={msg, _SubMsgName}, occurrence=Occurrence} ->
                      if Occurrence == optional, Value == undefined ->
                              Value;
                         true ->
                              remove_fields_by_skips(Value, DefsWithSkips)
                      end;
                  #gpb_oneof{fields=OFields} ->
                      case Value of
                          undefined ->
                              Value;
                          {OFName, Value2} ->
                              Pos = #?gpb_field.name,
                              case lists:keyfind(OFName, Pos, OFields) of
                                  #?gpb_field{type={msg, _SubMsgName}} ->
                                      {OFName, remove_fields_by_skips(
                                                 Value2, DefsWithSkips)};
                                  _ ->
                                      Value
                              end
                      end;
                  _ ->
                      Value
              end
              || {Value, Field} <- lists:zip(tl(tuple_to_list(Msg)), MsgDef),
                 Field /= skip],
    list_to_tuple([MsgName | Fields]).

remove_skips_from_defs(DefsWithSkips) ->
    [case Elem of
         {{enum,_}, _}=Enum ->
             Enum;
         {{msg,MsgName}, FieldsAndSkips} ->
             {{msg, MsgName}, remove_skips_recalculate_rnums(FieldsAndSkips)}
     end
     || Elem <- DefsWithSkips].

remove_skips_recalculate_rnums(FieldsAndSkips) ->
    {RecalculatedFieldsReversed, _TotalNumSkipped} =
        lists:foldl(
          fun(skip, {Fs, NumSkipped}) ->
                  {Fs, NumSkipped+1};
             (#?gpb_field{rnum=RNum}=F, {Fs, NumSkipped}) ->
                  {[F#?gpb_field{rnum=RNum-NumSkipped} | Fs], NumSkipped};
             (#gpb_oneof{rnum=RNum, fields=OFs}=F, {Fs, NumSkipped}) ->
                  OFs2 = [O#?gpb_field{rnum=RNum-NumSkipped} || O <- OFs],
                  F2 = F#gpb_oneof{rnum=RNum-NumSkipped,
                                   fields=OFs2},
                  {[F2 | Fs], NumSkipped}
          end,
          {[], 0},
          FieldsAndSkips),
    lists:reverse(RecalculatedFieldsReversed).

encoder_decoder(Mod) ->
    {oneof([gpb, Mod]),
     oneof([gpb, Mod]),
     [{copy_bytes,        oneof([false, true, auto, choose(2,4)])},
      {field_pass_method, oneof([pass_as_record, pass_as_params])}]}.

encode_msg(Msg, MsgDefs, Encoder) ->
    case Encoder of
        gpb -> gpb:encode_msg(Msg, MsgDefs);
        _   -> Encoder:encode_msg(Msg)
    end.

decode_msg(Bin, MsgName, MsgDefs, Decoder) ->
    case Decoder of
        gpb -> gpb:decode_msg(Bin, MsgName, MsgDefs);
        _   -> Decoder:decode_msg(Bin, MsgName)
    end.

merge_msgs(Msg1, Msg2, MsgDefs, Encoder, Decoder) ->
    if Encoder == gpb, Decoder == gpb ->
            gpb:merge_msgs(Msg1, Msg2, MsgDefs);
       Encoder /= gpb ->
            Encoder:merge_msgs(Msg1, Msg2);
       Decoder /= gpb ->
            Decoder:merge_msgs(Msg1, Msg2)
    end.

install_msg_defs(Mod, MsgDefs, Encoder, Decoder, COpts) ->
    if Encoder == gpb, Decoder == gpb ->
            ok; %% nothing needs to be done
       true ->
            install_msg_defs_aux(Mod, MsgDefs, COpts)
    end.

install_msg_defs(Mod, MsgDefs) ->
    install_msg_defs_aux(Mod, MsgDefs, [{copy_bytes, auto}]).

install_msg_defs_aux(Mod, MsgDefs, Opts) when is_list(Opts) ->
    Opts2 = [binary, {verify, always}, return_warnings | Opts],
    {{ok, Mod, Code, _},_} = {gpb_compile:msg_defs(Mod, MsgDefs, Opts2),
                              compile},
    ok = delete_old_versions_of_code(Mod),
    {{module, Mod},_} = {code:load_binary(Mod, "<nofile>", Code), load_code},
    ok.

delete_old_versions_of_code(Mod) ->
    code:purge(Mod),
    code:delete(Mod),
    code:purge(Mod),
    code:delete(Mod),
    ok.

msg_equals(Msg1, Msg2) ->
    case msg_approximately_equals(Msg1, Msg2) of
        true  ->
            true;
        false ->
            %% Run equals, even though we know it'll return
            %% false, because it'll show the messages
            %% appropritately -- e.g. not when shrinking.
            equals(Msg1,Msg2)
    end.

msg_approximately_equals(M1, M2) when is_tuple(M1), is_tuple(M2),
                                      element(1,M1) == element(1,M2),
                                      tuple_size(M1) == tuple_size(M2) ->
    lists:all(fun({F1, F2}) -> field_approximately_equals(F1, F2) end,
              lists:zip(tl(tuple_to_list(M1)),
                        tl(tuple_to_list(M2))));
msg_approximately_equals(_X, _Y) ->
    false.

field_approximately_equals(F1, F2) when is_float(F1), is_float(F2) ->
    is_float_equivalent(F1, F2);
field_approximately_equals(L1, L2) when is_list(L1), is_list(L2) ->
    lists:all(fun({E1,E2}) -> field_approximately_equals(E1,E2) end,
              lists:zip(L1,L2));
field_approximately_equals(X, X) ->
    true;
field_approximately_equals(Msg1, Msg2) when is_tuple(Msg1), is_tuple(Msg2) ->
    msg_approximately_equals(Msg1, Msg2);
field_approximately_equals(_X, _Y) ->
    io:format("Not equal: ~p <--> ~p~n", [_X, _Y]),
    false.

-define(ABS_ERROR, 1.0e-10). %% was: 1.0e-16
-define(REL_ERROR, 1.0e-6).  %% was: 1.0e-10

is_float_equivalent(F, F) -> true;
is_float_equivalent(F1,F2) ->
 if (abs(F1-F2) < ?ABS_ERROR) -> true;
    (abs(F1) > abs(F2)) -> abs( (F1-F2)/F1 ) < ?REL_ERROR;
    (abs(F1) < abs(F2)) -> abs( (F1-F2)/F2 ) < ?REL_ERROR
end.

is_within_percent(F1, F2, PercentsAllowedDeviation) ->
    AllowedDeviation = PercentsAllowedDeviation / 100,
    abs(F1 - F2) < (AllowedDeviation * F1).

get_create_tmpdir() ->
    D = filename:join("/tmp", f("~s-~s", [?MODULE, os:getpid()])),
    filelib:ensure_dir(filename:join(D, "dummy-file-name")),
    [file:delete(X) || X <- filelib:wildcard(filename:join(D,"*"))],
    D.

delete_tmpdir(TmpDir) ->
    [file:delete(X) || X <- filelib:wildcard(filename:join(TmpDir,"*"))],
    file:del_dir(TmpDir).

install_msg_defs_as_proto(MsgDefs, TmpDir) ->
    ProtoFile = filename:join(TmpDir, "x.proto"),
    ok = file:write_file(ProtoFile, msg_defs_to_proto(MsgDefs)).

msg_defs_to_proto(MsgDefs) ->
    iolist_to_binary(lists:map(fun msg_def_to_proto/1, MsgDefs)).

msg_def_to_proto({{enum, Name}, EnumValues}) ->
    f("enum ~s {~n"
      "~s"
      "}~n~n",
      [Name, lists:map(fun({N,V}) -> f("  ~s = ~w;~n", [N, V]) end,
                       EnumValues)]);
msg_def_to_proto({{msg, Name}, Fields}) ->
    f("message ~s {~n"
      "~s"
      "}~n~n",
      [Name, lists:map(fun(#?gpb_field{}=F) -> field_to_proto(F, true);
                          (#gpb_oneof{}=F) ->  oneof_to_proto(F)
                       end,
                       Fields)]).

field_to_proto(#?gpb_field{name=FName, fnum=FNum, type=Type, opts=Opts,
                           occurrence=Occurrence}, ShowOccurrence) ->
    Packed = lists:member(packed, Opts),
    f("  ~s ~s ~s = ~w~s;~n",
      [if ShowOccurrence     -> Occurrence;
          not ShowOccurrence -> "  "
       end,
       case Type of
           {msg,Name2} -> Name2;
           {enum,Name2} -> Name2;
           Type        -> Type
       end,
       FName,
       FNum,
       if Packed     -> " [packed=true]";
          not Packed -> ""
       end]).

oneof_to_proto(#gpb_oneof{name=FName, fields=OFields}) ->
    f("  oneof ~s {~n"
      "~s"
      "  };~n",
      [FName, [field_to_proto(OField, false) || OField <- OFields]]).

decode_then_reencode_via_protoc(GpbBin, Msg, TmpDir) ->
    ProtoFile = filename:join(TmpDir, "x.proto"),
    ETxtFile = filename:join(TmpDir, "x.etxt"),
    EMsgFile = filename:join(TmpDir, "x.emsg"),
    PMsgFile = filename:join(TmpDir, "x.pmsg"),
    TxtFile = filename:join(TmpDir, "x.txt"),
    MsgName = element(1, Msg),
    ok = file:write_file(ETxtFile, iolist_to_binary(f("~p~n", [Msg]))),
    ok = file:write_file(EMsgFile, GpbBin),
    DRStr = os:cmd(f("protoc --proto_path '~s'"
                     " --decode=~s '~s'"
                     " < '~s' > '~s'; echo $?~n",
                     [TmpDir, MsgName, ProtoFile, EMsgFile, TxtFile])),
    0 = list_to_integer(lib:nonl(DRStr)),
    ERStr = os:cmd(f("protoc --proto_path '~s'"
                     " --encode=~s '~s'"
                     " < '~s' > '~s'; echo $?~n",
                     [TmpDir, MsgName, ProtoFile, TxtFile, PMsgFile])),
    0 = list_to_integer(lib:nonl(ERStr)),
    {ok, ProtoBin} = file:read_file(PMsgFile),
    ProtoBin.


f(F,A) -> io_lib:format(F,A).
