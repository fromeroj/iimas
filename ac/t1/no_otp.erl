%%%---------------------------------------------------------------------------
%%% @doc A simple server that does not use OTP.
%%% @author Hans Christian v. Stockhausen <hc at vst.io>
%%% @end
%%%---------------------------------------------------------------------------
 
-module(no_otp).                     % module name (same as our erl filename,
                                     % i.e. no_otp.erl)
 
%% API
-export([                            % the functions we export - our API
  start/0,                           % - start new server process
  stop/0,                            % - stop server
  say_hello/0,                       % - print "Hello" to stdout
  get_count/0                        % - reply with number of times the main 
  ]).                                %   loop was executed
 
%% Callbacks
-export([init/0]).                   % exported so we can spawn it in start/0
                                     % listed as a separate export here as a
                                     % hint to clients not to use it
 
-define(SERVER, ?MODULE).            % SERVER macro is an alias for MODULE,
                                     % and expands to 'no_otp'
 
-record(state, {count}).             % record for our server state. Rather
                                     % arbitrarily we track how often the
                                     % main loop is run - see loop/1
 
 
%=============================================================================
% API - functions that our clients use to interact with the server
%=============================================================================
 
start() ->                           % spawn new process that calls init/0  
  spawn(?MODULE, init, []).          % the new process' PID is returned
 
stop() ->                            % send the atom stop to the process                           
  ?SERVER ! stop,                    % to instruct our server to shut down
  ok.                                % and return ok to caller
 
say_hello() ->                       % send the atom say_hello to the process
  ?SERVER ! say_hello,               % to print "Hello" to sdout
  ok.
 
get_count() ->                       % send callers Pid and the atom get_count
  ?SERVER ! {self(), get_count},     % to request counter value
  receive                            % wait for matching response and return
    {count, Value} -> Value          % Value to the caller
  end. 
 
 
%=============================================================================
% callback functions - not to be used by clients directly
%=============================================================================
 
init() ->                            % invoked by start/0
  register(?SERVER, self()),         % register new process PID under no_otp
  loop(#state{count=0}).             % start main server loop
 
%=============================================================================
% internal functions - note, these functions are not exported
%=============================================================================
 
loop(#state{count=Count}) ->         % the main server loop
  receive Msg ->                     % when API functions send a message
    case Msg of                      % check the atom contained
      stop ->                        % if atom is 'stop'
        exit(normal);                %   exit the process
      say_hello ->                   % if atom is 'say_hello'
        io:format("Hello~n");        %   write "Hello" to stdout
      {From, get_count} ->           % if Msg is tuple {Pid(), get_count}
        From ! {count, Count}        % reply with current counter value
    end                              %   in tagged tupple {count, Value}
  end,
  loop(#state{count = Count + 1}).   % recurse with updated state
