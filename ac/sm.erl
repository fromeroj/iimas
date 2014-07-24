-module(sm).  
-compile(export_all).

% Regresa una lista con elementos 0 y 1 de forma aleatoria
% ejm.  sm:rnd_lst(5) regresa una lista como [0,1,1,1,0]
rnd_lst(Size)->
    [random:uniform(2)-1 || _ <- lists:seq(1, Size)].

% Regresa una lista de tamaño Size, donde cada N elementos
% es un D y el resto V
% ejm sm:dot_lst(10,4,1,0) regresa [0,0,0,1,0,0,0,1,0,0]
dot_lst(Size,N,D,V)->
    A=fun(X) -> if ((X rem N) == 0) -> D;true -> V end end,
    [ A(X) || X <- lists:seq(1, Size)].

% Crea una "regla de wolfram" para AC lineales
% ej. (sm:wolf(90))(1,0,0) regresa 1 
wolf(N) -> 
    An=d2b(N),
    L=[ 0 || _ <- lists:seq(1,8 - length(An))]++An,
    fun(A,B,C) -> lists:nth(8-(A*4+B*2+C),L) end.
d2b(N)-> if  N < 2 -> [N]; true  -> d2b(N div 2)++[N rem 2] end.


% Calcula el automata celular lineal
% con un estado inicial L, funcion de transicion F
% y N pasos.
% ej.  sm:ac([1,1,0],sm:wolf(90),1).
% regresa [[1,1,0],[0,1,0]]
ac(Lst,_,0) -> [Lst];
ac(Lst,F,N) -> [Lst|ac(step(Lst,F),F,N-1)].
step(Lst,F) -> [A|[B|[C|T]]]=Lst, hlp(A,B,C,T,[],F).
hlp(A,B,C,Li,Lo,F)->
    if  Li ==[] -> [0]++lists:reverse([F(A,B,C)|Lo])++[0]; 
        true -> [H|T]=Li, hlp(B,C,H,T,[F(A,B,C)|Lo],F)
    end.

comp(Li,Lo)->
    if Li==[] -> lists:reverse(Lo);
       true -> [Hi|Lix]=Li,
               [Ho|_]=Lo,
               comp(Lix,[Ho*(Hi+1)|Lo])
    end.

price(N,Data) ->
    L=length(Data),
    L2=length(lists:nth(1,Data)),
    Sl=[ lists:nth(I,Data) || I <- lists:seq(1,L,N)],
    F=fun(Y) -> if Y < 0.375 -> -1; Y > 0.625 -> 1; true -> 0 end end,
    [H|Slp]=[ lists:sum(lists:map(F, X)) || X <- Sl ],
    K=[ (U+V)/L2 || {U,V} <-  lists:zip([H]++Slp,Slp++[0]) , V/=0 ],
    io:format("The value is: ~p.", [comp(K,[1.0])]),
    comp(K,[1.0]).

write_price(P)->
    {ok, IODevice} = file:open("/tmp/prices.txt", [write]), 
    Binaries = [ io_lib:format("~.2f",[Z]) ++", " || Z <- P],
    file:write(IODevice,Binaries),
    file:close(IODevice).
    
%Funciones de escritura
%w escribe en /tmp/foo.pgm y
%write recibe como primer parametro el archivo donde se escribira.
w(Data)-> write("/tmp/foo.pgm",Data).
write(File_name,Data)->
    {ok, IODevice} = file:open(File_name, [write]), 
    file:write(IODevice, "P2\n"),
    file:write(IODevice, "#Automata celular\n"),
    io:format(IODevice, "~w ~w~n\n",[length(lists:last(Data)),length(Data)]),
    file:write(IODevice, "65535\n"),
    F = fun(N) -> if N==0 -> 0; N==1 -> 65535; true -> round(N*256*256) end end,
    Binaries = [[integer_to_list(F(Z))++" " || Z <- X]++"\n" || X <- Data],
    file:write(IODevice,Binaries),
    file:close(IODevice).

% Escribe archivo de difusion.
%sm:w(sm:ac(sm:dot_lst(100,41,1,0),fun(A,B,C)-> 0.1*(A+C)+0.8*B end,100)).
%sm:write_price(sm:price(10,sm:ac(sm:rnd_lst(1000),fun(A,B,C)->0.1*(A+C)+0.8*B end,10000)))

%sm:write_price(sm:price(10,sm:ac(sm:rnd_lst(1000),sm:wolf(30),10000))).
