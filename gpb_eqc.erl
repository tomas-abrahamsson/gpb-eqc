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
                          | 'bytes' | {'msg',atom()} | 'packed'
                          | 'fixed32' | 'sfixed32' | 'float'.

-record(field,
        {name       :: atom(),
         fnum       :: integer(),
         rnum       :: pos_integer(), %% field number in the record
         type       :: gpb_field_type(),
         occurrence :: 'required' | 'optional' | 'repeated',
         opts       :: [term()]
        }).

message_def() ->
    %% CAn we have messages that refer to themselves?
    %% Actually not if field is required, since then we cannot generate
    %% a message of that kind.
    %% left_of/1 guarantees that the messages only refer to earlier definitions
    ?LET(MsgNames,eqc_gen:non_empty(list(message_name())),
	 begin
	     UMsgNames = lists:usort(MsgNames),
	     [ {{msg,Msg},message_fields(left_of(Msg,UMsgNames))} 
	       || Msg<-UMsgNames]
	 end).

left_of(X,Xs) ->
    lists:takewhile(fun(Y) ->
			    Y/=X
		    end,Xs).

message_fields(MsgNames) ->
    %% can we have definitions without any field?
    ?LET(FieldDefs,eqc_gen:non_empty(
		     list({field_name(),
			   elements([required,optional,repeated])})),
	 begin
	     UFieldDefs = unique(FieldDefs),
	     [ #field{name=Field,fnum=length(FieldDefs)-Nr,rnum=Nr+1,
		      type= type(MsgNames),
		      occurrence=Occurrence,
		      opts= case Occurrence of
				repeated ->
				    elements([[],[packed]]);
				_ ->
				    []
			    end}|| 
		 {{Field,Occurrence},Nr}<-lists:zip(
			       UFieldDefs,
			       lists:seq(1,length(UFieldDefs)))]
	 end).

unique([]) ->
    [];
unique([{Key,Value}|Rest]) ->
    [{Key,Value}|unique([ {K,V} || {K,V}<-Rest, K/=Key])].

message_name() ->
    elements([m1,m2,m3,m4,m5,m6]).

field_name() ->
    elements([a,b,c,field1,f]).

type([]) ->
    elements([bool,sint32,sint64,int32,int64,uint32,
	      uint64
	      %% {'enum',atom()}
	      %% fixed64,sfixed64,double,string,
	      %% bytes,
	      %% fixed32,
	      %% sfixed32,
	      %% float
	     ]);
type(MsgNames) ->
    ?LET(MsgName,elements(MsgNames),
	 elements([bool,sint32,sint64,int32,int64,uint32,
		   uint64, 
		   %% {'enum',atom()}
		   %% fixed64,sfixed64,double,string,
		   %% bytes,
		   {'msg',MsgName}
		   %% fixed32,
		   %% sfixed32,
		   %% float
		  ])).

enum() ->
    {{enum,e},[#field{}]}.


%% generator for messages that respect message definitions

message(MessageDefs) ->
    ?LET({{msg,Msg},_Fields},oneof(MessageDefs),
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
    uint(64).

sint(Base) ->
    int(Base).

int(Base) ->
    ?LET(I,uint(Base),
	 begin 
	     << N:Base/signed >> = <<I:Base>>, N 
	 end).

uint(Base) ->
    oneof([ choose(0,exp(B)-1) || B<-lists:seq(1,Base)]).

exp(1) ->
    2;
exp(N) ->
    2*exp(N-1).



%%% properties

prop_encode_decode() ->
    ?FORALL(MsgDef,message_def(),
	    ?FORALL(Msg,message(MsgDef),
		    begin
			Bin = gpb:encode_msg(Msg,MsgDef),
			DecodedMsg = gpb:decode_msg(Bin,element(1,Msg),MsgDef),
			equals(Msg,DecodedMsg)
		    end)).

prop_merge() ->
    ?FORALL(MsgDef,message_def(),
	?FORALL(Msg,oneof([ M || {{_,M},_}<-MsgDef]),
	    ?FORALL({Msg1,Msg2},{message(Msg,MsgDef),message(Msg,MsgDef)},
		    collect({Msg1,Msg2},
		    begin
			MergedMsg = gpb:merge_msgs(Msg1,Msg2,MsgDef),
			Bin1 = gpb:encode_msg(Msg1,MsgDef),
			Bin2 = gpb:encode_msg(Msg2,MsgDef),
			DecodedMerge =  
			    gpb:decode_msg(<<Bin1/binary,Bin2/binary>>,
					   Msg,MsgDef),
			equals(MergedMsg, DecodedMerge)
                    end)))).
