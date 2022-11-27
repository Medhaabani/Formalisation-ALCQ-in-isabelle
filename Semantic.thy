theory Semantic imports Syntax 

begin

text{* we introduce the definition of the interpretation, in this definition
  domain is a set. This set must be not empty. I think that we can propose a new
  definition where the interp_c has thye (nc \<Rightarrow> subset of domain ) interp_r is set of
  pairs.  *}

typedecl domtype
  (* consts domaine :: "domtype set" *)
  (* 
  record ('ni, 'nr, 'nc) Interp =
  domaine ::  "domtype set"
  interp_c :: "'nc \<Rightarrow> domtype set "
  interp_r :: "'nr \<Rightarrow>  (domtype  * domtype) set"
  interp_inst :: "'ni \<Rightarrow> domtype "
  *)

record ('nr, 'nc) Interp =
  domaine ::  "domtype set"
  interp_c :: "'nc \<Rightarrow> domtype set "
  interp_r :: "'nr \<Rightarrow>  (domtype  * domtype) set"


  (*  interprtation of instance *)


types 'ni Interp_inst = "'ni \<Rightarrow> domtype "

text{* interpretation of role *}

fun interpR  :: " ('nr, 'nc) Interp \<Rightarrow> 'nr role \<Rightarrow> (domtype  * domtype) set"
  where
  "interpR  i (AtomR b) = (interp_r i)  b"
  (*| " interpR i (Inv r ) =  {(x,y). (y,x) \<in> (interpR i r)}  " *)
 

text{* interpretation of concpt:
  
  In the theory of DL, the interpetation of Top is the domain. (here we use
  UNIV): but if we put "interpC i Top = domaine ", we can't proof the lemma
  interTop_interNotBottom (mybe others) becouse the complement of empty set is
  UNIV.  The complement in "interpC NotC c", is the complement of "interpC i
  c" to univ or to what?  We can too delete bottom and top from the definition
  of concept (syntax).  Let first work with this definition *}

fun interpC :: "('nr, 'nc) Interp \<Rightarrow> ('nr, 'nc) concept \<Rightarrow> domtype set"
  where
  "interpC i Bottom = {}"
  | "interpC i Top = UNIV "
  | "interpC i (AtomC a) = interp_c i a"
  | "interpC i (AndC c1 c2) = (interpC i c1) \<inter>  (interpC  i c2)"
  | "interpC i (OrC c1 c2) = (interpC i c1) \<union> (interpC  i c2)"
  | "interpC i (NotC c) = - (interpC  i c)"
  |"interpC i (AllC r c) = {x . \<forall> y. ((x,y) \<in>  (interpR i  r ) \<longrightarrow> y \<in> (interpC i c ))  }" 
  |"interpC i (SomeC r c) ={ x. \<exists> y.   ((x,y) \<in>  (interpR i  r ) \<and>   y \<in>  (interpC  i c ))}"


text {* proofs\<dots>., verification the correctenss of this  specification  *}

lemma sem_and_commutative:
  "interpC i (AndC c1 c2) = interpC i (AndC c2 c1)"
  by auto


lemma sem_or_commutative:
  "interpC i (OrC c1 c2) = interpC i (OrC c2 c1)"
  by auto

lemma sem_and_or:  
  "interpC i (AndC c1 c2) = interpC i (NotC (OrC (NotC c1) (NotC c2)))"
  by simp 


lemma sem_or_and:
  "interpC i (OrC c1 c2) = interpC i (NotC (AndC( NotC c1) (NotC c2)))"
  by simp

lemma  inter_c_and_not_c:
  "interpC i (AndC c1 (NotC c1)) = {}"
  by simp
 
lemma interTop_interNotBottom:
  " interpC i Top = interpC i (NotC Bottom)" 
  by auto

lemma  inter_c_eq_inter_not_not_c:
  "interpC i c = interpC i (NotC (NotC c))"
  by simp

lemma inter_C_or_not_c:
  "(interpC i (OrC  c1 (NotC c1))) = UNIV"
  by auto

lemma sem_all_some : 
  "(interpC i  (AllC r c)) = (interpC i  (NotC (SomeC  r (NotC c))))"
  by  auto

    (********************************************************************)
    (***************** satisfiability, subsumption  and model ************)
    (*********************************************************************)

text {* definition of model (is_model i c) it means that the interpretation i
  is model for c *}

definition is_model :: "('nr, 'nc) Interp \<Rightarrow> ('nr, 'nc) concept  \<Rightarrow> bool"
  where 
  " is_model  i c  \<equiv> (interpC i c) \<noteq> {}"

text {* can we define it as function? *}

fun is_model_fun :: "('nr, 'nc) Interp \<Rightarrow> ('nr, 'nc) concept  \<Rightarrow> bool"
  where 
  " is_model_fun  i c  = ((interpC i c) \<noteq> {})"

lemma Top_has_model: 
  "is_model_fun i Top "
  by  simp

lemma Top_has_model_def: 
  "is_model i Top "
  by  (simp add: is_model_def)
  

text{************************************************************************
  a concept c is satisfiable if: Exists i such that i is model (if we want to
  use the definition of model). or exists i such that the (interpC i c) is not
  empty set this definition not yet given
  ***************************************************************************}

definition satisfiable_def :: "('nr, 'nc) concept \<Rightarrow> bool"
  where 
  "satisfiable_def c  \<equiv>  \<exists> i. is_model i c  "

definition satisfiable :: "('nr, 'nc) concept \<Rightarrow> bool"
  where 
  "satisfiable c  \<equiv>  \<exists> i. (interpC i c) \<noteq> {} "

lemma "satisfiable Top"
by (simp add: satisfiable_def)

text {* definition of subsomption 
  we say that the concept c is subsumed  by D if  forall i,  interp i c \<inclus> interC i c *}

definition subsumes :: "('nr, 'nc) concept \<Rightarrow> ('nr, 'nc) concept \<Rightarrow> bool"
  where 
  " subsumes  c1 c2  \<equiv>  \<forall> i. (interpC i c1) \<subseteq> (interpC i c2) "

definition equiv_semantic :: "('nr, 'nc) concept \<Rightarrow> ('nr, 'nc) concept \<Rightarrow> bool"
  where 
  " equiv_semantic  c1 c2  \<equiv>  \<forall> i. (interpC i c1) = (interpC i c2) "

text{* some equivalances subsu satisfi *}

lemma  Top_sub_all :
  "subsumes  c Top"
  by (simp add : subsumes_def)

lemma sub_to_sat : 
  " subsumes c1 c2 \<longrightarrow>  satisfiable (OrC (NotC c1) c2)"
  apply (simp add : satisfiable_def subsumes_def)
  apply blast
  done

lemma sub_to_unsat : 
  " subsumes c1 c2 \<longrightarrow> \<not>  satisfiable (AndC  c1 (NotC c2))"
  apply (simp add : satisfiable_def subsumes_def)
  apply blast
  done

lemma unsat_to_sub:
  "\<not>  satisfiable (AndC  c1 (NotC c2)) \<longrightarrow> subsumes c1 c2 "
  apply (simp add : satisfiable_def subsumes_def)
  apply blast
  done

lemma unsat_eq_sub : 
  "\<not> satisfiable (AndC  c1 (NotC c2)) \<longleftrightarrow>  (subsumes c1 c2)"
  apply (rule iffI)
  apply (simp add : unsat_to_sub )
  apply (simp add : sub_to_unsat )
  done

lemma equi_to_sub: 
  "equiv_semantic c1 c2 \<longrightarrow> (subsumes c1 c2) \<and> (subsumes c2 c1)"
by (simp add : equiv_semantic_def subsumes_def)


lemma sub_to_equi: 
  "(subsumes c1 c2) \<and> (subsumes c2 c1) \<longrightarrow> equiv_semantic c1 c2"
  apply (simp add : equiv_semantic_def subsumes_def)
  apply blast
  done

lemma equi_eq_sub :
  "equiv_semantic c1 c2 \<longleftrightarrow>(subsumes c1 c2 \<and> subsumes c2 c1)"
  apply (rule iffI)
  apply (simp add : equi_to_sub )
  apply (simp add : sub_to_equi )
  done

(***********transformation of  negation ******************************)

fun  trans_neg ::  "('nr, 'nc) concept \<Rightarrow> ('nr, 'nc) concept" 
  where   
  "trans_neg (AtomC x) = NotC (AtomC x)"
  | "trans_neg Top         =   Bottom"
  | "trans_neg Bottom      =   Top "
  | "trans_neg (NotC c)    =    c"
  | "trans_neg (AndC c d)  = OrC (trans_neg c)(trans_neg d)" 
  | "trans_neg (OrC c d)   = AndC (trans_neg c)(trans_neg d)"
  | "trans_neg (AllC r c)  = SomeC r (trans_neg c)"
  | "trans_neg (SomeC r c) = AllC r (trans_neg c)"
		

  (********************************)
lemma trans_neg_andc:
  " (trans_neg (AndC c0 c1))= OrC (trans_neg c0) (trans_neg c1)"
  apply auto
  done
(**********************************************************)
(********** negation  normal forme ******************)
fun NNF ::  "('nr, 'nc) concept \<Rightarrow> ('nr, 'nc) concept" 
 where
  "NNF (NotC c1)  =  trans_neg (NNF c1)"
 |"NNF (AtomC x)  = AtomC x"
 |"NNF Top        = Top"
 |"NNF Bottom     = Bottom"
 |"NNF( AndC c1 c2) = AndC (NNF c1 ) (NNF c2)"
 |"NNF (OrC c1 c2)  = OrC (NNF c1) (NNF c2)"
 |"NNF (AllC  r c)  = AllC r (NNF c)"
 |"NNF (SomeC r c)  = SomeC r (NNF c)"

(**** Extraction ***)
(*export_code NNF in OCaml file "nnf.ml "*)

lemma  sem_neg: 
  "(interpC i (trans_neg c))  = (- (interpC i c))"
  apply (induct c)
  apply auto
  done

lemma  sem_NNF_C_is_C : 
  "(interpC i  c)  =  (interpC i  (NNF c))"
  apply (induct c)
  apply (simp add: sem_neg)+
  done

fun  isNF :: "('nr, 'nc) concept \<Rightarrow> bool" 
where
  "isNF (AtomC x) = True"
  |"isNF Top = True"
  |"isNF Bottom = True" 
  |"isNF (NotC c1) =  (\<exists> x. (c1 = (AtomC x)))"
  |"isNF (AndC c1 c2) =(isNF c1 \<and>  isNF c2) "
  |"isNF (OrC c1 c2) =  (isNF c1  \<and>  isNF c2)"
  |"isNF (AllC  r c) = isNF c"
  |"isNF (SomeC r c) = isNF c"

lemma isNF_to_NNF :
  "isNF c \<longrightarrow> ((NNF c ) = c)"
  apply (induct c)
  apply auto
  done

    (* MS: rule_format converts an object implication \<longrightarrow>
    into a meta-implication \<Longrightarrow> that is better for rewriting *)
lemma isnf_trans_neg [rule_format]:
  " isNF c \<longrightarrow>  isNF (trans_neg c)"
by (induct c) auto


    (* MS: repeated application of a rule with + *)
lemma isnf_nnf: 
  "  isNF (NNF c )"
  apply (induct c)
  apply (simp add : isnf_trans_neg)+
  done

    (* MS: "insert" inserts an instance of a lemma, with
    instantiation given by the "of" clause (instances of variables 
    in the order of occurrence in lemma isnf_nnf *)

lemma  NNF_to_isNF:
  "(NNF c = c) \<Longrightarrow> isNF c"
  apply (insert isnf_nnf [of c] )
  apply simp
  done

lemma isnf_eq_nnf : 
  "isNF c \<longleftrightarrow> ((NNF c ) = c)"
  apply (rule iffI)
  apply (simp add: isNF_to_NNF)
  apply (simp add: NNF_to_isNF)
  done

end


