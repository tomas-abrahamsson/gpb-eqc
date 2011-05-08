%%% File    : gpb_eqc.erl
%%% Author  : Thomas Arts <thomas.arts@quviq.com>
%%% Description : Testing protocol buffer implemented by Tomas Abrahamsson
%%% Created : 12 May 2010 by Thomas Arts

-module(gpb_eqc).

-include_lib("eqc/include/eqc.hrl").

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
     {timeout, 120,  %% timeout for all tests
      [{timeout, 60, %% timeout for each test
        [{atom_to_list(Prop),
          fun() -> true = eqc:quickcheck(?MODULE:Prop()) end}]}
       || Prop <- PropsToTest]}}.

is_property("prop_"++_, 0) -> true;
is_property(_, _)          -> false.


-type gpb_field_type() :: 'sint32' | 'sint64' | 'int32' | 'int64' | 'uint32'
                          | 'uint64' | 'bool' | {'enum',atom()}
                          | 'fixed64' | 'sfixed64' | 'double' | 'string'
                          | 'bytes' | {'msg',atom()}
                          | 'fixed32' | 'sfixed32' | 'float'.

-record(field,
        {name       :: atom(),
         fnum       :: integer(),
         rnum       :: pos_integer(), %% field number in the record
         type       :: gpb_field_type(),
         occurrence :: 'required' | 'optional' | 'repeated',
         is_packed = false :: boolean(),
         opts = []  :: [term()]
        }).

message_defs() ->
    %% Can we have messages that refer to themselves?
    %% Actually not if field is required, since then we cannot generate
    %% a message of that kind.
    %% left_of/1 guarantees that the messages only refer to earlier definitions
    %% Enums are globabbly unique. Hence, we generate them globabbly
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
    ?LET(FieldDefs, eqc_gen:non_empty(
                      list({field_name(),
                            elements([required, optional, repeated]),
                            msg_field_type(MsgNames, EnumNames)})),
         begin
             UFieldDefs = keyunique(1, FieldDefs),
             [begin
                  Packed = case {Occurrence, Type} of
                               {repeated, {msg,_}}    -> false;
                               {repeated, string}     -> false;
                               {repeated, bytes}      -> false;
                               {repeated, _Primitive} -> elements([false,true]);
                               _                      -> false
                           end,
                  #field{name=Field,fnum=length(FieldDefs)-Nr+1,rnum=Nr+1,
                         type=Type,
                         occurrence=Occurrence,
                         is_packed=Packed}
              end
              || {{Field,Occurrence,Type},Nr}
                     <-lists:zip(UFieldDefs, lists:seq(1,length(UFieldDefs)))]
         end).

keyunique(_N, []) ->
    [];
keyunique(N, [Tuple|Rest]) ->
    [Tuple| keyunique(N, [ T2 || T2<-Rest, element(N,T2)/=element(N,Tuple)])].

message_name() ->
    elements([m1,m2,m3,m4,m5,m6]).

field_name() ->
    elements([a,b,c,field1,f]).


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
%% enum file_open_return_values { enoent = 1, exxx=2 }
unique_values([],_N) ->
    [];
unique_values([Cons|Conss],N) ->
    ?LET(Next,nat(),
         [ {Cons,N} | unique_values(Conss,Next+N+1) ]).

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
    FieldValues =
        [ value(Field#field.type,Field#field.occurrence,MessageDefs) ||
            Field<-Fields],
    list_to_tuple([Msg|FieldValues]).

value(Type,optional,MessageDefs) ->
    default(undefined,value(Type,MessageDefs));
value(Type,repeated,MessageDefs) ->
    list(value(Type,MessageDefs));
value(Type,required,MessageDefs) ->
    value(Type,MessageDefs).

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
    list(unicode_code_point()).

unicode_code_point() ->
    %% range 0 -> 10FFFF
    ?SUCHTHAT(CP, oneof([uint(16), choose(16#10000, 16#10FFFF)]),
              (CP < 16#D800) orelse (CP > 16#DFFF)).

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
            ?FORALL({Msg, Encoder, Decoder, CopyBytes},
                    {message(MsgDefs), oneof([gpb, code]), oneof([gpb, code]),
                     oneof([false, true, auto, choose(2,4)])},
                    begin
                        if Encoder == code; Decoder == code ->
                                ok = install_msg_defs(Mod, MsgDefs, CopyBytes);
                           true ->
                                ok
                        end,
                        Bin = case Encoder of
                                  gpb  -> gpb:encode_msg(Msg, MsgDefs);
                                  code -> Mod:encode_msg(Msg)
                              end,
                        MsgName = element(1, Msg),
                        DecodedMsg =
                            case Decoder of
                                gpb  -> gpb:decode_msg(Bin,MsgName,MsgDefs);
                                code -> Mod:decode_msg(Bin,MsgName)
                            end,
                        ?WHENFAIL(io:format("~p /= ~p\n",[Msg,DecodedMsg]),
                                  msg_approximately_equals(Msg,DecodedMsg))
                    end)).

prop_encode_decode_via_protoc() ->
    Mod = gpb_eqc_m,
    ?FORALL(MsgDefs,message_defs(),
            ?FORALL({Msg,Encoder, Decoder},
                    {message(MsgDefs), oneof([gpb, code]), oneof([gpb, code])},
                    begin
                        if Encoder == code; Decoder == code ->
                                ok = install_msg_defs(Mod, MsgDefs);
                           true ->
                                ok
                        end,
                        TmpDir = get_create_tmpdir(),
                        ProtoFile = filename:join(TmpDir, "x.proto"),
                        ETxtFile = filename:join(TmpDir, "x.etxt"),
                        EMsgFile = filename:join(TmpDir, "x.emsg"),
                        PMsgFile = filename:join(TmpDir, "x.pmsg"),
                        TxtFile = filename:join(TmpDir, "x.txt"),
                        MsgName = element(1, Msg),
                        file:write_file(ETxtFile, iolist_to_binary(
                                                    f("~p~n", [Msg]))),
                        file:write_file(ProtoFile, msg_defs_to_proto(MsgDefs)),
                        GpbBin = case Encoder of
                                      gpb  -> gpb:encode_msg(Msg,MsgDefs);
                                      code -> Mod:encode_msg(Msg)
                                  end,
                        file:write_file(EMsgFile, GpbBin),
                        DRStr = os:cmd(f("protoc --proto_path '~s'"
                                         " --decode=~s '~s'"
                                         " < '~s' > '~s'; echo $?~n",
                                         [TmpDir,
                                          MsgName, ProtoFile,
                                          EMsgFile, TxtFile])),
                        0 = list_to_integer(lib:nonl(DRStr)),
                        ERStr = os:cmd(f("protoc --proto_path '~s'"
                                         " --encode=~s '~s'"
                                         " < '~s' > '~s'; echo $?~n",
                                         [TmpDir,
                                          MsgName, ProtoFile,
                                          TxtFile, PMsgFile])),
                        0 = list_to_integer(lib:nonl(ERStr)),
                        {ok, ProtoBin} = file:read_file(PMsgFile),
                        DecodedMsg =
                            case Decoder of
                                gpb  -> gpb:decode_msg(ProtoBin,MsgName,MsgDefs);
                                code -> Mod:decode_msg(ProtoBin,MsgName)
                            end,
                        ?WHENFAIL(io:format("~p /= ~p\n",[Msg,DecodedMsg]),
                                  msg_approximately_equals(Msg, DecodedMsg))
                    end)).

prop_encode_decode_with_skip() ->
    Mod1 = gpb_eqc_m1,
    Mod2 = gpb_eqc_m2,
    ?FORALL(
       MsgDefs, message_defs(),
       ?FORALL(
          {DefsSubset, InitialMsg, Encoder, Decoder, CopyBytes},
          {message_subset_defs(MsgDefs),
           message(MsgDefs),
           oneof([gpb, code]),
           oneof([gpb, code]),
           oneof([false, true, auto, choose(2,4)])},
          begin
              if Encoder == code; Decoder == code ->
                      ok = install_msg_defs(Mod1, MsgDefs, CopyBytes),
                      ok = install_msg_defs(Mod2, DefsSubset, CopyBytes);
                 true ->
                      ok
              end,
              Encoded1 = case Encoder of
                             gpb  -> gpb:encode_msg(InitialMsg, MsgDefs);
                             code -> Mod1:encode_msg(InitialMsg)
                         end,
              MsgName = element(1, InitialMsg),
              Decoded1 = case Decoder of
                                  gpb  -> gpb:decode_msg(Encoded1,MsgName,DefsSubset);
                                  code -> Mod2:decode_msg(Encoded1,MsgName)
                              end,
              Encoded2 = case Encoder of
                             gpb  -> gpb:encode_msg(Decoded1, DefsSubset);
                             code -> Mod2:encode_msg(Decoded1)
                         end,
              Decoded2 = case Decoder of
                             gpb  -> gpb:decode_msg(Encoded2,MsgName,DefsSubset);
                             code -> Mod2:decode_msg(Encoded2,MsgName)
                         end,
              ?WHENFAIL(io:format("~p /= ~p\n",[Decoded1,Decoded2]),
                        msg_approximately_equals(Decoded1, Decoded2))
          end)).

message_subset_defs(MsgDefs) ->
    [case Elem of
         {{enum,_}, _}=Enum ->
             Enum;
         {{msg,MsgName}, MsgFields} ->
             {{msg, MsgName}, msg_fields_subset(MsgFields)}
     end
     || Elem <- MsgDefs].

msg_fields_subset(Fields) ->
    eqc_gen:non_empty(
      ?LET(Fields2, [elements([Field, skip]) || Field <- Fields],
           recalculate_rnums(Fields2))).

recalculate_rnums(FieldsAndSkips) ->
    {RecalculatedFieldsReversed, _TotalNumSkipped} =
        lists:foldl(fun(skip, {Fs, NumSkipped}) ->
                            {Fs, NumSkipped+1};
                       (#field{rnum=RNum}=F, {Fs, NumSkipped}) ->
                            {[F#field{rnum=RNum-NumSkipped} | Fs], NumSkipped}
                    end,
                    {[], 0},
                    FieldsAndSkips),
    lists:reverse(RecalculatedFieldsReversed).

install_msg_defs(Mod, MsgDefs) ->
    install_msg_defs(Mod, MsgDefs, auto).

install_msg_defs(Mod, MsgDefs, CopyBytes) ->
    Opts = [binary, {copy_bytes, CopyBytes}],
    {{ok, Mod, Code, _},_} = {gpb_compile:msg_defs(Mod, MsgDefs, Opts),compile},
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


prop_merge() ->
    Mod = gpb_eqc_m,
    ?FORALL(MsgDefs,message_defs(),
        ?FORALL(Msg,oneof([ M || {{msg,M},_}<-MsgDefs]),
            ?FORALL({Msg1,Msg2,Encoder1, Encoder2, Decoder, CopyBytes},
                    {message(Msg,MsgDefs), message(Msg,MsgDefs),
                     oneof([gpb,code]), oneof([gpb,code]), oneof([gpb,code]),
                     oneof([false, true, auto, choose(2,4)])},
                    begin
                        ok = install_msg_defs(Mod, MsgDefs, CopyBytes),
                        MergedMsg = Mod:merge_msgs(Msg1,Msg2),
                        Bin1 = case Encoder1 of
                                   gpb  -> gpb:encode_msg(Msg1, MsgDefs);
                                   code -> Mod:encode_msg(Msg1)
                               end,
                        Bin2 = case Encoder2 of
                                   gpb  -> gpb:encode_msg(Msg2, MsgDefs);
                                   code -> Mod:encode_msg(Msg2)
                               end,
                        MergedBin = <<Bin1/binary,Bin2/binary>>,
                        DecodedMerge = case Decoder of
                                           gpb  -> gpb:decode_msg(MergedBin,Msg,
                                                                  MsgDefs);
                                           code -> Mod:decode_msg(MergedBin,Msg)
                                       end,
                        msg_equals(MergedMsg, DecodedMerge)
                    end))).

get_create_tmpdir() ->
    D = filename:join("/tmp", f("~s-~s", [?MODULE, os:getpid()])),
    filelib:ensure_dir(filename:join(D, "dummy-file-name")),
    [file:delete(X) || X <- filelib:wildcard(filename:join(D,"*"))],
    D.

delete_tmpdir(TmpDir) ->
    [file:delete(X) || X <- filelib:wildcard(filename:join(TmpDir,"*"))],
    file:del_dir(TmpDir).

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
      [Name, lists:map(
               fun(#field{name=FName, fnum=FNum, type=Type, is_packed=Packed,
                          occurrence=Occurrence}) ->
                       f("  ~s ~s ~s = ~w~s;~n",
                         [Occurrence,
                          case Type of
                              {msg,Name2} -> Name2;
                              {enum,Name2} -> Name2;
                              Type        -> Type
                          end,
                          FName,
                          FNum,
                          if Packed     -> " [packed=true]";
                             not Packed -> ""
                          end])
               end,
               Fields)]).

f(F,A) -> io_lib:format(F,A).
