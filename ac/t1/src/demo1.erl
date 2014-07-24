-module(demo1).
-export([fact/1]).

-spec fact(N::pos_integer()) -> pos_integer().
fact(0) ->1;
fact(N) -> N* fact(N-1).


