-module(atm_fixed_atm_fixed).



%% ----------------------------------------
%% Import helper functions

-export([act_ptp_A_19/0,
	act_ptp_B_19/0,
	act_ptp_C_19/0,
	act_ptp_A_14/0,
	act_ptp_B_14/0,
	act_ptp_C_14/0,
	act_ptp_A_11/0,
	act_ptp_B_11/0,
	act_ptp_C_11/0,
	ptp_A_fun/0,
	ptp_B_fun/0,
	ptp_C_fun/0,
	main/0,
	sel_act/4,
	loop_sel/3]).

%% ----------------------------------------
%% The code to chose a branch...trivial for the moment

-import(rgg_support,
	[notify/3,
	getBranch/2,
	getBranch/1,
	debug/4,
	debugLoop/0,
	lookup/2,
	smartReg/3]).



sel_act(_, CP, P, Branch) ->
%% choose one of the branches
   Sel = Branch(),
   %% send the selection to each participant
   notify(CP, Sel, P).


loop_sel(CP, P, V) ->
   case V of
      0 ->
         lists:foreach(fun(X) -> X ! {CP, exitLoop} end, P),
         rgg_support:debug("exiting loop ~p", [CP], rgg_support:debugLoop(), 10);
      _ ->
         lists:foreach(fun(X) -> rgg_support:debug("[~p] 	 ~p ! loopBack", [CP, X], 1, 10), X ! {CP, loopBack} end, P),
         rgg_support:debug("looping back ~p. V = ~p", [CP, V], rgg_support:debugLoop(), 10),
         loop_sel(CP, P, V - 1)
   end.



%% ----------------------------------------
%% ptp_A at the branching 11

act_ptp_A_11() ->
   receive
      {11, branch_1} ->
                  receive {10, allow} ->         debug("[~p]   ~p ? ~p : ~p", [10, ptp_B, ptp_A, [allow]], 1, 10)end,
         debug("[~p]   ~p ! ~p : ~p", [9, ptp_A, ptp_C, [money]], 1, 10),
         ptp_C ! {9, money};
      {11, branch_2} ->
                  receive {8, deny} ->         debug("[~p]   ~p ? ~p : ~p", [8, ptp_B, ptp_A, [deny]], 1, 10)end,
         debug("[~p]   ~p ! ~p : ~p", [7, ptp_A, ptp_C, [bye]], 1, 10),
         ptp_C ! {7, bye}
   end.

%% ----------------------------------------
%% ptp_B at the branching 11

act_ptp_B_11() ->
   receive
      {11, branch_1} ->
                  debug("[~p]   ~p ! ~p : ~p", [10, ptp_B, ptp_A, [allow]], 1, 10),
         ptp_A ! {10, allow};
      {11, branch_2} ->
                  debug("[~p]   ~p ! ~p : ~p", [8, ptp_B, ptp_A, [deny]], 1, 10),
         ptp_A ! {8, deny}
   end.

%% ----------------------------------------
%% ptp_C at the branching 11

act_ptp_C_11() ->
   receive
      {11, branch_1} ->
                  receive {9, money} ->         debug("[~p]   ~p ? ~p : ~p", [9, ptp_A, ptp_C, [money]], 1, 10)end;
      {11, branch_2} ->
                  receive {7, bye} ->         debug("[~p]   ~p ? ~p : ~p", [7, ptp_A, ptp_C, [bye]], 1, 10)end
   end.

%% ----------------------------------------
%% ptp_A at the branching 14

act_ptp_A_14() ->
   receive
      {14, branch_1} ->
                  receive {13, withdraw} ->         debug("[~p]   ~p ? ~p : ~p", [13, ptp_C, ptp_A, [withdraw]], 1, 10)end,
         debug("[~p]   ~p ! ~p : ~p", [12, ptp_A, ptp_B, [authWithdrawal]], 1, 10),
         ptp_B ! {12, authWithdrawal},
         act_ptp_A_11();
      {14, branch_2} ->
                  receive {6, checkBalance} ->         debug("[~p]   ~p ? ~p : ~p", [6, ptp_C, ptp_A, [checkBalance]], 1, 10)end,
         debug("[~p]   ~p ! ~p : ~p", [5, ptp_A, ptp_B, [getBalance]], 1, 10),
         ptp_B ! {5, getBalance},
         receive {4, balance} ->         debug("[~p]   ~p ? ~p : ~p", [4, ptp_B, ptp_A, [balance]], 1, 10)end,
         debug("[~p]   ~p ! ~p : ~p", [3, ptp_A, ptp_C, [balance]], 1, 10),
         ptp_C ! {3, balance};
      {14, branch_3} ->
                  receive {2, quit} ->         debug("[~p]   ~p ? ~p : ~p", [2, ptp_C, ptp_A, [quit]], 1, 10)end,
         debug("[~p]   ~p ! ~p : ~p", [1, ptp_A, ptp_B, [quit]], 1, 10),
         ptp_B ! {1, quit}
   end.

%% ----------------------------------------
%% ptp_B at the branching 14

act_ptp_B_14() ->
   receive
      {14, branch_1} ->
                  receive {12, authWithdrawal} ->         debug("[~p]   ~p ? ~p : ~p", [12, ptp_A, ptp_B, [authWithdrawal]], 1, 10)end,
         spawn(atm_fixed_atm_fixed, sel_act, [[], 11, [ptp_A, ptp_B, ptp_C], fun() -> getBranch([11, branching_table], bra) end]),
         act_ptp_B_11();
      {14, branch_2} ->
                  receive {5, getBalance} ->         debug("[~p]   ~p ? ~p : ~p", [5, ptp_A, ptp_B, [getBalance]], 1, 10)end,
         debug("[~p]   ~p ! ~p : ~p", [4, ptp_B, ptp_A, [balance]], 1, 10),
         ptp_A ! {4, balance};
      {14, branch_3} ->
                  receive {1, quit} ->         debug("[~p]   ~p ? ~p : ~p", [1, ptp_A, ptp_B, [quit]], 1, 10)end
   end.

%% ----------------------------------------
%% ptp_C at the branching 14

act_ptp_C_14() ->
   receive
      {14, branch_1} ->
                  debug("[~p]   ~p ! ~p : ~p", [13, ptp_C, ptp_A, [withdraw]], 1, 10),
         ptp_A ! {13, withdraw},
         act_ptp_C_11();
      {14, branch_2} ->
                  debug("[~p]   ~p ! ~p : ~p", [6, ptp_C, ptp_A, [checkBalance]], 1, 10),
         ptp_A ! {6, checkBalance},
         receive {3, balance} ->         debug("[~p]   ~p ? ~p : ~p", [3, ptp_A, ptp_C, [balance]], 1, 10)end;
      {14, branch_3} ->
                  debug("[~p]   ~p ! ~p : ~p", [2, ptp_C, ptp_A, [quit]], 1, 10),
         ptp_A ! {2, quit}
   end.

%% ----------------------------------------
%% ptp_A at the branching 19

act_ptp_A_19() ->
   receive
      {19, branch_1} ->
                  receive {18, denied} ->         debug("[~p]   ~p ? ~p : ~p", [18, ptp_B, ptp_A, [denied]], 1, 10)end,
         debug("[~p]   ~p ! ~p : ~p", [17, ptp_A, ptp_C, [authFail]], 1, 10),
         ptp_C ! {17, authFail};
      {19, branch_2} ->
                  receive {16, granted} ->         debug("[~p]   ~p ? ~p : ~p", [16, ptp_B, ptp_A, [granted]], 1, 10)end,
         debug("[~p]   ~p ! ~p : ~p", [15, ptp_A, ptp_C, [granted]], 1, 10),
         ptp_C ! {15, granted},
         act_ptp_A_14()
   end.

%% ----------------------------------------
%% ptp_B at the branching 19

act_ptp_B_19() ->
   receive
      {19, branch_1} ->
                  debug("[~p]   ~p ! ~p : ~p", [18, ptp_B, ptp_A, [denied]], 1, 10),
         ptp_A ! {18, denied};
      {19, branch_2} ->
                  debug("[~p]   ~p ! ~p : ~p", [16, ptp_B, ptp_A, [granted]], 1, 10),
         ptp_A ! {16, granted},
         act_ptp_B_14()
   end.

%% ----------------------------------------
%% ptp_C at the branching 19

act_ptp_C_19() ->
   receive
      {19, branch_1} ->
                  receive {17, authFail} ->         debug("[~p]   ~p ? ~p : ~p", [17, ptp_A, ptp_C, [authFail]], 1, 10)end;
      {19, branch_2} ->
                  receive {15, granted} ->         debug("[~p]   ~p ? ~p : ~p", [15, ptp_A, ptp_C, [granted]], 1, 10)end,
         spawn(atm_fixed_atm_fixed, sel_act, [[], 14, [ptp_A, ptp_B, ptp_C], fun() -> getBranch([14, branching_table], bra) end]),
         act_ptp_C_14()
   end.

%% ----------------------------------------
%% Coordinating start / end of ptp_A

ptp_A_fun() ->
   receive {go, Pid} ->
            receive {21, auth} ->      debug("[~p]   ~p ? ~p : ~p", [21, ptp_C, ptp_A, [auth]], 1, 10)end,
      debug("[~p]   ~p ! ~p : ~p", [20, ptp_A, ptp_B, [authReq]], 1, 10),
      ptp_B ! {20, authReq},
      act_ptp_A_19(),
      Pid ! done_actor
   end.


%% ----------------------------------------
%% Coordinating start / end of ptp_B

ptp_B_fun() ->
   receive {go, Pid} ->
            receive {20, authReq} ->      debug("[~p]   ~p ? ~p : ~p", [20, ptp_A, ptp_B, [authReq]], 1, 10)end,
      spawn(atm_fixed_atm_fixed, sel_act, [[], 19, [ptp_A, ptp_B, ptp_C], fun() -> getBranch([19, branching_table], bra) end]),
      act_ptp_B_19(),
      Pid ! done_actor
   end.


%% ----------------------------------------
%% Coordinating start / end of ptp_C

ptp_C_fun() ->
   receive {go, Pid} ->
            debug("[~p]   ~p ! ~p : ~p", [21, ptp_C, ptp_A, [auth]], 1, 10),
      ptp_A ! {21, auth},
      act_ptp_C_19(),
      Pid ! done_actor
   end.


%% ----------------------------------------
%% Let's start...

main() ->
   case lists:member(branching_table, ets:all()) of
      true -> ets:delete(branching_table);
      _ -> noTable
   end,
   ets:new(branching_table, [set, named_table, public]),
   ets:insert(branching_table, {19, 2}),
   ets:insert(branching_table, {14, 3}),
   ets:insert(branching_table, {11, 2}),
   ets:insert(branching_table,{debug,10}),
   smartReg(ptp_A, spawn(atm_fixed_atm_fixed, ptp_A_fun, []), 10),
   smartReg(ptp_B, spawn(atm_fixed_atm_fixed, ptp_B_fun, []), 10),
   smartReg(ptp_C, spawn(atm_fixed_atm_fixed, ptp_C_fun, []), 10),
   STime = os:system_time(),
   ptp_A ! {go, self()},
   ptp_B ! {go, self()},
   ptp_C ! {go, self()},
   receive done_actor -> ok end,
   receive done_actor -> ok end,
   receive done_actor -> ok end,
   file:write_file(".time.tmp", integer_to_list(os:system_time() - STime))
.