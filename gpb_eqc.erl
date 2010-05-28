%%% File    : gpb_eqc.erl
%%% Author  : Thomas Arts <thomas.arts@quviq.com>
%%% Description : Testing protocol buffer implemented by Tomas Abrahamsson
%%% Created : 12 May 2010 by Thomas Arts

-module(gpb_eqc).

-include_lib("eqc/include/eqc.hrl").

-compile(export_all).


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
         opts       :: [term()]
        }).

message_defs() ->
    %% CAn we have messages that refer to themselves?
    %% Actually not if field is required, since then we cannot generate
    %% a message of that kind.
    %% left_of/1 guarantees that the messages only refer to earlier definitions
    ?LET(EnumNames,list(enum_name()),
         ?LET(MsgNames,eqc_gen:non_empty(list(message_name())),
              begin
                  UEnumNames = lists:usort(EnumNames),
                  UMsgNames = lists:usort(MsgNames),
                  EnumDefs = [ {{enum,Enum}, enumvalues(Enum)}
                               || Enum<-UEnumNames],
                  EnumDefs ++
                      [ {{msg,Msg},message_fields(left_of(Msg,UMsgNames),
                                                  UEnumNames)}
                        || Msg<-UMsgNames]
              end)).

left_of(X,Xs) ->
    lists:takewhile(fun(Y) ->
			    Y/=X
		    end,Xs).

message_fields(MsgNames, EnumNames) ->
    %% can we have definitions without any field?
    ?LET(FieldDefs,eqc_gen:non_empty(
		     list({field_name(),
			   elements([required,optional,repeated]),
                           msg_field_type(MsgNames, EnumNames)})),
	 begin
	     UFieldDefs = keyunique(1, FieldDefs),
	     [ #field{name=Field,fnum=length(FieldDefs)-Nr+1,rnum=Nr+1,
		      type=Type,
		      occurrence=Occurrence,
		      opts= case {Occurrence, Type} of
				{repeated, {msg,_}} ->
                                    [];
				{repeated, string} ->
                                    [];
				{repeated, bytes} ->
                                    [];
				{repeated, _Primitive} ->
				    elements([[], [packed]]);
				_ ->
				    []
			    end}||
		 {{Field,Occurrence,Type},Nr}<-lists:zip(
			       UFieldDefs,
			       lists:seq(1,length(UFieldDefs)))]
	 end).

keyunique(_N, []) ->
    [];
keyunique(N, [Tuple|Rest]) ->
    [Tuple| keyunique(N, [ T2 || T2<-Rest, element(N,T2)/=element(N,Tuple)])].

message_name() ->
    elements([m1,m2,m3,m4,m5,m6]).

field_name() ->
    elements([a,b,c,field1,f]).

enum_name() ->
    elements([e1,e2,e3,e4,e5,e6]).

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

enumvalues(EnumName) ->
    ?LET(Vs, eqc_gen:non_empty(list(enumvalue(EnumName))),
         keyunique(2, (keyunique(1, Vs)))).

enumvalue(EnumName) ->
    ?LET(E, {enumeratorname(EnumName), nat()},
         E).

enumeratorname(EnumName) ->
    elements([list_to_atom(atom_to_list(EnumName)++"_"++atom_to_list(S))
              || S <- [x1, x2, x3, x4, x5, x6, x7]]).


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
    ?FORALL(MsgDefs,message_defs(),
	    ?FORALL(Msg,message(MsgDefs),
		    begin
			Bin = gpb:encode_msg(Msg,MsgDefs),
			DecodedMsg = gpb:decode_msg(Bin,element(1,Msg),MsgDefs),
			equals(Msg,DecodedMsg)
		    end)).

prop_encode_decode_via_protoc() ->
    ?FORALL(MsgDefs,message_defs(),
	    ?FORALL(Msg,message(MsgDefs),
		    begin
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
                        file:write_file(EMsgFile, gpb:encode_msg(Msg,MsgDefs)),
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
                        DecodedMsg = gpb:decode_msg(ProtoBin,MsgName,MsgDefs),
                        case msg_approximately_equals(Msg, DecodedMsg) of
                            true  ->
                                delete_tmpdir(TmpDir),
                                true;
                            false ->
                                %% Run equals, even though we know it'll return
                                %% false, because it'll show the messages
                                %% appropritately -- e.g. not when shrinking.
                                equals(Msg,DecodedMsg)
                        end
		    end)).

msg_approximately_equals({M, Fields1}, {M, Fields2}) when length(Fields1) ==
                                                          length(Fields2) ->
    lists:all(fun({F1, F2}) -> field_approximately_equals(F1, F2) end,
              lists:zip(Fields1, Fields2));
msg_approximately_equals(_, _) ->
    false.

field_approximately_equals(F1, F2) when is_float(F1), is_float(F2) ->
    is_within_percent(F1, F2, 0.001);
field_approximately_equals(X, X) ->
    true;
field_approximately_equals(Msg1, Msg2) when is_tuple(Msg1), is_tuple(Msg2) ->
    msg_approximately_equals(Msg1, Msg2);
field_approximately_equals(_, _) ->
    false.

is_within_percent(F1, F2, PercentsAllowedDeviation) ->
    AllowedDeviation = PercentsAllowedDeviation / 100,
    abs(F1 - F2) < (AllowedDeviation * F1).


prop_merge() ->
    ?FORALL(MsgDefs,message_defs(),
	?FORALL(Msg,oneof([ M || {{msg,M},_}<-MsgDefs]),
	    ?FORALL({Msg1,Msg2},{message(Msg,MsgDefs),message(Msg,MsgDefs)},
		    begin
			MergedMsg = gpb:merge_msgs(Msg1,Msg2,MsgDefs),
			Bin1 = gpb:encode_msg(Msg1,MsgDefs),
			Bin2 = gpb:encode_msg(Msg2,MsgDefs),
			DecodedMerge =
			    gpb:decode_msg(<<Bin1/binary,Bin2/binary>>,
					   Msg,MsgDefs),
			equals(MergedMsg, DecodedMerge)
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
               fun(#field{name=FName, fnum=FNum, type=Type,
                          occurrence=Occurrence, opts=Opts}) ->
                       f("  ~s ~s ~s = ~w~s;~n",
                         [Occurrence,
                          case Type of
                              {msg,Name2} -> Name2;
                              {enum,Name2} -> Name2;
                              Type        -> Type
                          end,
                          FName,
                          FNum,
                          case lists:member(packed,Opts) of
                              true  -> " [packed=true]";
                              false -> ""
                          end])
               end,
               Fields)]).

f(F,A) -> io_lib:format(F,A).
