%% Implementation of Zeevat's Constructive Optimality Theory Syntax,
%% based on Bresnan's Optimal Syntax


%% All constraints implemented, except for fp-complements.
%% I'm assuming these will be solved by a more complete lexicon.
%% For the simple example sentences given here (and in the Zeevat paper)
%% it makes no difference either way.

:- op(500, xfx, ':').

%% Main predicate for derivation
%% from input feature structure.
derive(InputFS,OutputFS) :-
  cc_max(InputFS,CCMAX),
  op_spec(CCMAX,OPSPEC),
  heads(OPSPEC,HEADS),
  ob_head(HEADS,OBHEAD),
  fp_complements(OBHEAD,FPCOMP),
  lp_complements(FPCOMP,LPCOMP),
  agr(LPCOMP,AGR),
  neg_to_i(AGR,NEGTOI),
  remove_syn(NEGTOI,OutputFS).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Constraints                                   %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Clause that represents CC+MAX constraints.
cc_max(Input, Output) :-

   %% First give the terminal node entry (the actual word)
   %% from the predicate functor
   func_find(Input,[:,pred,PredicateFS]), %% Find the predicate's sub-FS in the total FS
   func_find(PredicateFS,[:,pred,PredicateWithArguments]), %% Find the predicate with its arguments in the predicate's sub-FS
   PredicateWithArguments =.. [Predicate|ArgumentList], % Separate predicate from arguments
   unify(Input, [pred:[lex:Predicate|_]|_], FS1), %% Add actual predicate word to FS of pred

   %% Next instantiate the governable functions
   %% (arguments of the predicate),
   %% which at the moment are variables
   gf_list(GFList),
   length(ArgumentList,Length),
   first(GFList,Length,TrimmedGFList),
   list_to_FS(TrimmedGFList,GFFS),
   unify(FS1,GFFS),

   %% Then mark the operator explicitly
   member_open_list(operator:_,GFFS),
   !,
   func_find(GFFS,[:,operator,[H|_]]),
   H=..[:,OperatorMode,OperatorGF],
   unify(GFFS,[OperatorGF:[mode:OperatorMode|_]|_],FS2),

   %% Lastly, give the terminal node entry for the predicate's arguments.
   %% lex_list(FS2, ArgumentList, Output).
   lex_unify(FS2, Output).
cc_max(Input, Output) :-
   %% First give the terminal node entry (the actual word)
   %% from the predicate functor
   func_find(Input,[:,pred,PredicateFS]), %% Find the predicate's sub-FS in the total FS
   func_find(PredicateFS,[:,pred,PredicateWithArguments]), %% Find the predicate with its arguments in the predicate's sub-FS
   PredicateWithArguments =.. [Predicate|ArgumentList], % Separate predicate from arguments
   unify(Input, [pred:[lex:Predicate|_]|_], FS1), %% Add actual predicate word to FS of pred

   %% Next instantiate the governable functions
   %% (arguments of the predicate),
   %% which at the moment are variables
   gf_list(GFList),
   length(ArgumentList,Length),
   first(GFList,Length,TrimmedGFList),
   list_to_FS(TrimmedGFList,GFFS),
   unify(FS1,GFFS),

   lex_unify(GFFS, Output).

%% Clause that represents OP-SPEC constraint
op_spec(Input, Output) :-
  %% first find the term that is identified by the operator
  member_open_list(operator:_,Input),
  !,
  func_find(Input,[:,operator,[_:OperatorTerm|_]]),

  %% next put that term in scp position
  unify(Input,[OperatorTerm:[syn:scp|_],syn:[cp:[scp:filled|_]|_]|_],Output),
  !.
op_spec(FS, FS) :- !.

%% Clause that represents HEADS constraint
heads(Input, Output) :-
  rem_vars(Input,NoVars), %% make a closed list for passing to heads_adder/3
  heads_adder(NoVars, Input, Output),
  !.
  
%% heads_adder/3: helper predicate for heads/2
%% iterates through closed top-level list of FS
%% and puts lexical heads in HXP position
heads_adder([], FS, FS).
heads_adder([Term:SubFS|T],FullInputFS,OutputFS) :-
  member_open_list(lex:_,SubFS),
  func_find(SubFS,[:,lex,Word]),
  category(Word,Category),
  concat_atom([h,Category,p],HXP),
  concat_atom([Category,p],XP),
  \+ Term = syn,
  \+ Term = operator,
  unify(FullInputFS, [Term:[syn:HXP|_], syn:[XP:[HXP:filled|_]|_]|_], IntermediateFS),
  !,
  heads_adder(T, IntermediateFS, OutputFS).
heads_adder([_|T], InputFS, OutputFS) :-
  heads_adder(T, InputFS, OutputFS).
  
%% Clause that represents OB-HEAD constraint
ob_head(Input,Output) :-
  %% First check for existence of scp but not hcp
  func_find(Input,[:,syn,SYN]),
  func_find(SYN,[:,cp,CP]),
  member_open_list(scp:filled,CP),
  \+ member_open_list(hcp:filled,CP),

  %% If scp exists, but not hcp, insert a dummy and fill hcp
  unify(Input,[dummy:[cat:aux,lex:do, syn:hcp|_],syn:[cp:[hcp:filled|_] |_] |_],Output),
  !.
ob_head(FS,FS) :- !.

%% Clause that represents FP-COMPLEMENTS
%% inserts auxiliaries if tense calls for them
%% for do-support in past tense (with negation),
%% morphology is also supplied right here instead
%% of the agreement constraint
fp_complements(Input, Output) :-
  func_find(Input,[:,tense,Tense]),
  Tense = fut,
  !,
  remove_element(dummy:_, Input, TrimmedFS), % remove the dummy if it exists
  unify(TrimmedFS,[dummy:[cat:aux,lex:will,syn:hip|_],syn:[ip:[hip:filled|_] |_] |_],Output).
fp_complements(Input, Output) :-
  func_find(Input,[:,neg,NegFS]),
  member_open_list(neg:true,NegFS),
  member_open_list(tense:prs, Input),
  !,
  remove_element(dummy:_, Input, TrimmedFS), % remove the dummy if it exists
  unify(TrimmedFS,[dummy:[cat:aux,lex:do, syn:hip|_],syn:[ip:[hip:filled|_] |_] |_],Output).
fp_complements(Input, Output) :-
  func_find(Input,[:,neg,NegFS]),
  member_open_list(neg:true,NegFS),
  member_open_list(tense:pst, Input),
  !,
  remove_element(dummy:_, Input, TrimmedFS), % remove the dummy if it exists
  unify(TrimmedFS,[dummy:[cat:aux,lex:did, syn:hip|_],syn:[ip:[hip:filled|_] |_] |_],Output).
fp_complements(FS,FS) :- !.
  


%% Clause that represents LP-COMPLEMENTS constraint
lp_complements(Input,Output) :-
  find_governable_functions(Input,ListOfGovernableFunctions), %% Returns a list of governable functions by looking at the predicate
  argv_adder(ListOfGovernableFunctions,1,Input,Output),  %% Puts each GF in argvN if it doesn't have a syntactic position yet
  !.

%% find_governable_functions(+FeatureStructure,-ListOfGovernableFunctions)
%% helper predicate for lp_complements
%% Given a feature structure, returns a list of governable functions, by
%% looking at the predicate
find_governable_functions(FeatureStructure,ListOfGovernableFunctions) :-
  func_find(FeatureStructure,[:,pred,PredSubFS]),
  func_find(PredSubFS,[:,pred,FullPred]),
  FullPred=..[_|ListOfGovernableFunctions].

%% argv_adder(+ListOfGovernableFunctions, +CurrentN, +InputFeatureStructure, -OutputFeatureStructure)
%% argv_adder/4 adds argvN to each governable function in the list
%% helper predicate for lp_complements
argv_adder([], _, FS, FS).
argv_adder([HeadGF|RestGF],N,FullFS,OutputFS) :-
   func_find(FullFS, [:,HeadGF,GFsubFS]),
   \+ member_open_list(syn:_,GFsubFS),
   !,
   concat_atom([vparg,N],ARGVN),
   unify(FullFS, [HeadGF:[syn:ARGVN|_]|_], IntermediateFS),
   N1 is N + 1,
   argv_adder(RestGF,N1,IntermediateFS,OutputFS).
argv_adder([_|RestGF], N, FullFS, OutputFS) :-
   argv_adder(RestGF, N, FullFS, OutputFS).

%% Clause that represents AGR constraint
agr(Input, Output) :-
  %% Assign a synactic position to the subject
  assign_syn_to_subj(Input, IntermediateFS),
  %% Get the agreement feature that fits the subject
  agreement(IntermediateFS, AgreementFeature),
  %% Find the first (as in topmost projection) head
  find_first_head(IntermediateFS, Functor),
  %% and assign the agreement feature as the value to this head's morphology feature
  unify(IntermediateFS,[Functor:[morph:AgreementFeature|_]|_],Output),
  !.


%% assign_syn_to_subj(+FeatureStructure,-NewFeatureStructure)
%% Does the first part of agr, i.e. assigns a syntactic position to the subject
assign_syn_to_subj(Input,Output) :-
   func_find(Input,[:,syn,SynSubFS]),
   member_open_list(ip:_,SynSubFS),
   !,
   func_find(Input,[:,subj,SubjSubFS]),
   remove_element(syn:_, SubjSubFS, TrimmedSubjSubFS),
   unify(TrimmedSubjSubFS, [syn:sip|_], NewSubjSubFS),
   remove_element(subj:_, Input, IntermediateFS),
   unify(IntermediateFS,[subj:NewSubjSubFS, syn:[ip:[sip:filled|_]|_]|_], Output).
assign_syn_to_subj(Input, Output) :-
   func_find(Input,[:,subj,SubjSubFS]),
   remove_element(syn:_, SubjSubFS, TrimmedSubjSubFS),
   unify(TrimmedSubjSubFS, [syn:ssu|_], NewSubjSubFS),
   remove_element(subj:_, Input, IntermediateFS),
   unify(IntermediateFS,[subj:NewSubjSubFS|_], Output).

%% agreement(+FeatureStructure,-agreementfeature)
%% does the second part of agr, i.e. returns the agreement feature
%% that matches the subject.
agreement(FeatureStructure, s) :-
  member_open_list(tense:prs, FeatureStructure),
  func_find(FeatureStructure,[:,subj,SubjSubFS]),
  member_open_list(pers:3,SubjSubFS),
  member_open_list(num:sg,SubjSubFS),
  !.
agreement(FeatureStructure, ed) :-
  member_open_list(tense:pst, FeatureStructure),
  member_open_list(neg:[neg:false|_], FeatureStructure),
  !.
agreement(_,0) :- !.


%% find_first_head(+FeatureStructure, -TopmostHeadInTree)
%% returns the highest head in the tree
find_first_head(FeatureStructure, Head) :-
  rem_vars(FeatureStructure, NoVars),
  findall(A,all_func_find(NoVars,[:,A,_]),FunctorList),
  find_first(FunctorList, FeatureStructure, Head).

%% find_first/3: helper predicate for find_first_head
%% find_first works by multiple iterations through the functor list
%% bit clunky but works.
find_first([],_,_) :- fail.
%% First iteration, looking for hcp:
find_first([FirstFunctor|_], FeatureStructure, Head) :-
   func_find(FeatureStructure, [:, FirstFunctor, FunctorSubFS]),
   member_open_list(syn:hcp,FunctorSubFS),
   !,
   Head = FirstFunctor.
find_first([_|Rest], FeatureStructure, Head) :-
   find_first(Rest, FeatureStructure, Head).
%%  Second iteration, looking for hip:
find_first([FirstFunctor|_], FeatureStructure, Head) :-
   func_find(FeatureStructure, [:, FirstFunctor, FunctorSubFS]),
   member_open_list(syn:hip,FunctorSubFS),
   !,
   Head = FirstFunctor.
find_first([_|Rest], FeatureStructure, Head) :-
   find_first(Rest, FeatureStructure, Head).
%% Third iteration, looking for hvp
find_first([FirstFunctor|_], FeatureStructure, Head) :-
   func_find(FeatureStructure, [:, FirstFunctor, FunctorSubFS]),
   member_open_list(syn:hvp,FunctorSubFS),
   !,
   Head = FirstFunctor.
find_first([_|Rest], FeatureStructure, Head) :-
   find_first(Rest, FeatureStructure, Head).


%% Clause the represents Neg-to-I
neg_to_i(Input,Output) :-
  member_open_list(neg:[neg:true|_],Input), %% Is this sentence negated?
  !,
  unify(Input,[neg:[syn:i_adjunct|_]|_],Output).
neg_to_i(FS,FS).

%% Last in series of constraints, removes the placeholder syn: position
%% in the top level of the feature structure.
remove_syn(Input,Output) :-
  remove_element(syn:_,Input,Output).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% General helper predicates                     %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

projections_list([scp,hcp,sip,hip,i_adjunct,ssu,hvp,vparg1,vparg2,vparg3]).
readable_output(InputFS) :-
  %% Search through FS from top to bottom
  projections_list(List),
  projections(List, InputFS).

projections([], _).
projections([CurrentNode|Rest],FeatureStructure) :-
  search_nodes(CurrentNode, FeatureStructure),
  projections(Rest, FeatureStructure).
  
search_nodes(_,[]) :- !.
search_nodes(Node, [_:SubFS|_]) :-
  member_open_list(syn:_, SubFS),
  func_find(SubFS, [:,syn,SYN]),
  Node = SYN,
  member_open_list(morph:_,SubFS),
  !,
  func_find(SubFS, [:,lex,LEX]),
  write(LEX),
  func_find(SubFS, [:,morph,MORPH]),
  write('-'),
  write(MORPH),
  write(' ').
search_nodes(Node, [_:SubFS|_]) :-
  member_open_list(syn:_, SubFS),
  func_find(SubFS, [:,syn,SYN]),
  Node = SYN,
  !,
  func_find(SubFS, [:,lex,LEX]),
  write(LEX),
  write(' ').
search_nodes(Node, [_|RestOfFeatureStructure]) :-
  search_nodes(Node, RestOfFeatureStructure).

  
  
  
%% unify/3:
%% Destructive unification algorithm for feature structures,
%% based on Gazdar & Mellish, Blackburn & Striegnitz
%% Consists of 2 mutually recursive clauses (different from G&M),
%% unify/2 and pathvalue/4, and a wrapper unify/3 which takes care of
%% special cases with empty feature structures.
unify([],FS,FS) :- !.
unify(FS,[],FS) :- !.
unify(FS1,FS2,FS1) :-
  unify(FS1,FS2).
unify(FS,FS) :- !.
unify([Feature:Value|Rest],FS) :-
  pathvalue(Feature,Value,FS,RestOfFS),
  unify(Rest,RestOfFS).

pathvalue(Feature, Value1, [Feature:Value2|Rest], Rest) :-
  !,
  unify(Value1, Value2).
pathvalue(Feature, Value, [FS|Rest], [FS|NewRest]) :-
  !,
  pathvalue(Feature, Value, Rest, NewRest).


%% Weak version of above destructive unification algorithm
%% Succeeds also if unification fails, in that case the
%% third argument is simply the first.
weak_unify(FS1, FS2, Result) :-
  unify(FS1,FS2,Result),
  !.
weak_unify(FS1,_,FS1).

%% membership check on open list, works by instantiating
%% variables and then memberchecking
member_open_list(Element,OpenList) :-
  \+ (instantiate(OpenList),
    \+ (member(Element,OpenList))).

%% instantiate variables, helper predicate for member_open_list/2
instantiate(F) :-
        inst_vars0(F,s(0),_).
inst_vars0(F,I,s(I)) :-
        var(F),!,
        F = I.
inst_vars0([],I,I) :- !.
inst_vars0([H|T],I,IOut) :- !,
        inst_vars0(H,I,I0),
        inst_vars0(T,I0,IOut).
inst_vars0(_F:V,I,IOut) :- !,
        inst_vars0(V,I,IOut).
inst_vars0(_,I,I).



%% remove_element(+Element, +List, -Result)
%% wrapper predicate to remove elements from
%% open feature structures.
%% used in agr
remove_element(Element, List, Result) :-
  rem_vars(List,NoVars),
  rem_element(Element, NoVars, ResultAsList),
  list_to_FS(ResultAsList,Result),
  !.
rem_element(_,[],[]).
rem_element(Element,[Head|Tail], [Head|Result]) :-
  \+ Element = Head,
  !,
  rem_element(Element,Tail,Result).
rem_element(Element,[_|T],Result) :-
  rem_element(Element,T,Result).

%% non-destructive removal of variables from list
%% NB: only removes variables on top level of structure
%% rem_vars(InputFS,OutputFS)
rem_vars(FS,[]) :-
  var(FS),
  !.
rem_vars([H|T],[H|ResultTail]) :-
  \+ var(H),
  !,
  rem_vars(T,ResultTail).
rem_vars([H|T],Result) :-
  var(H),
  !,
  rem_vars(T,Result).
rem_vars([],[]).


%% List of governable functions in the order
%% that they appear in the predicate.
%% can be modified or expanded without problems
gf_list([subj:_,dir_obj:_,ind_obj:_]).

%% first/3:
%% OutputList contains only the first N elements of InputList
first(InputList,N,OutputList) :-
  first(InputList,0,N,OutputList).
first(_,N,N,[]) :- !.
first([H|T],Index,Max,[H|Result]) :-
  Index < Max,
  NewIndex is Index + 1,
  first(T,NewIndex,Max,Result).

%% list_to_FS(+List,-FeatureStructure)
list_to_FS([X],[X|_]) :- !.
list_to_FS([H|T],[H|Tail]):-
  list_to_FS(T,Tail).

all_func_find([H|_],Functor) :-
  H=..Functor.
all_func_find([_|T],Functor) :-
  all_func_find(T,Functor).

%% search list (feat struc) for functors & arguments for functors
func_find([H|_],FunctorAsList) :-
  H =.. FunctorAsList,
  !. % there will be only one solution for this application
func_find([_|T],FunctorAsList) :-
  func_find(T,FunctorAsList).
func_find([],_) :- !, fail.

%% Clunky predicate to unify inputstructure with all
%% entries in lexicon to instantiate the terminal node
%% values
lex_unify(InputFS,OutputFS) :-
  they(They),
  weak_unify(InputFS,They,FS1),
  what(What),
  weak_unify(FS1,What,FS2),
  he(He),
  weak_unify(FS2,He,FS3),
  him(Him),
  weak_unify(FS3,Him,FS4),
  neg(Neg),
  weak_unify(FS4,Neg,OutputFS),
  %% etc. for other lexical items.
  !.


  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% A tiny bit of lexicon                         %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% Some categories
verb(read).
verb(hit).
verb(insult).
category(Word,Category) :-
  verb(Word),
  Category = v.

%%% Some lexical feature structures:
they([subj:[pred:pro,num:pl,pers:3,lex:they|_]|_]).
what([dir_obj:[pred:pro,num:sg,pers:3,gend:n,mode:q,lex:what|_]|_]).
he([subj:[pred:pro,num:sg,pers:3,gend:m,lex:he|_]|_]).
him([dir_obj:[pred:pro,num:sg,pers:3,gend:m,lex:him|_]|_]).
neg([neg:[neg:true,lex:not|_]|_]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Two example sentences                         %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% what do they read
input1([
  operator:[q:GF2|_],
  pred:[pred:read(GF1,GF2)|_],
  GF1:[pred:pro,
       num:pl,
       pers:3 |_],
  GF2:[pred:pro,
       num:sg,
       pers:3,
       gend:n
       |_],
  tense:prs,
  neg:[neg:false|_]
  |_]).

%% he will not hit him
input2([
  pred:[pred:hit(GF1,GF2)|_],
  GF1:[pred:pro,
       num:sg,
       pers:3 |_],
  GF2:[pred:pro,
       num:sg,
       pers:3,
       gend:m
       |_],
  tense:fut,
  neg:[neg:true|_]
  |_]).

%% he insults him
input3([
  pred:[pred:insult(GF1,GF2)|_],
  GF1:[pred:pro,
       num:sg,
       pers:3 |_],
  GF2:[pred:pro,
       num:sg,
       pers:3,
       gend:m
       |_],
  tense:prs,
  neg:[neg:false|_]
  |_]).

%% he does not insult him
input4([
  pred:[pred:insult(GF1,GF2)|_],
  GF1:[pred:pro,
       num:sg,
       pers:3 |_],
  GF2:[pred:pro,
       num:sg,
       pers:3,
       gend:m
       |_],
  tense:prs,
  neg:[neg:true|_]
  |_]).
  
%% he insulted him
input5([
  pred:[pred:insult(GF1,GF2)|_],
  GF1:[pred:pro,
       num:sg,
       pers:3 |_],
  GF2:[pred:pro,
       num:sg,
       pers:3,
       gend:m
       |_],
  tense:pst,
  neg:[neg:false|_]
  |_]).

%% he did not insult him
input6([
  pred:[pred:insult(GF1,GF2)|_],
  GF1:[pred:pro,
       num:sg,
       pers:3 |_],
  GF2:[pred:pro,
       num:sg,
       pers:3,
       gend:m
       |_],
  tense:pst,
  neg:[neg:true|_]
  |_]).

full_derivation(X) :-
  cc_max(X,Y),
  write('CC+MAX:'),
  nl,
  write(Y),
  nl,
  op_spec(Y,OPSPEC),
  write('OP-SPEC: '),
  nl,
  write(OPSPEC),
  nl,
  heads(OPSPEC,HEADS),
  write('HEADS: '),
  nl,
  write(HEADS),
  nl,
  ob_head(HEADS,OBHEAD),
  write('OB-HEADS: '),
  nl,
  write(OBHEAD),
  fp_complements(OBHEAD, FPCOMPLEMENTS),
  nl,
  write('FP-COMPLEMENTS: '),
  nl,
  write(FPCOMPLEMENTS),
  lp_complements(FPCOMPLEMENTS, LPCOMPLEMENTS),
  nl,
  write('LP-COMPLEMENTS: '),
  nl,
  write(LPCOMPLEMENTS),
  %assert(lpcomplements(LPCOMPLEMENTS)),
  agr(LPCOMPLEMENTS,AGR),
  nl,
  write('AGR: '),
  nl,
  write(AGR),
  neg_to_i(AGR,NEGTOI),
  nl,
  write('NEG TO I: '),
  nl,
  write(NEGTOI),
  remove_syn(NEGTOI,FINAL),
  nl,
  write('FINAL FEATURE STRUCTURE: '),
  nl,
  write(FINAL),
  nl,
  write('Generated sentence: '),
  nl,
  readable_output(FINAL).

example1 :-
  input1(X),nl,write('Input structure: '),nl,write(X),nl,
  full_derivation(X).
example2 :-
  input2(X),nl,write('Input structure: '),nl,write(X),nl,
  full_derivation(X).
example3 :-
  input3(X),nl,write('Input structure: '),nl,write(X),nl,
  full_derivation(X).
example4 :-
  input4(X),nl,write('Input structure: '),nl,write(X),nl,
  full_derivation(X).
example5 :-
  input5(X),nl,write('Input structure: '),nl,write(X),nl,
  full_derivation(X).
example6 :-
  input6(X),nl,write('Input structure: '),nl,write(X),nl,
  full_derivation(X).
  
:- write('Final version of program. Type "example1" through "example6." to see full derivation of example sentences.'),nl.