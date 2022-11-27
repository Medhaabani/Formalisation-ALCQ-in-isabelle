theory Termination imports Aux Tableau Multiset 
begin



  (* --------------------------------------------------  *)
  (* General theorems about mult, setsum, pair_leq etc.  *)
  (* --------------------------------------------------  *)

lemma setsum_insert_split: "finite F \<Longrightarrow> 
  setsum f (insert a F) = 
  (if a \<in> F then setsum f F else f a + setsum f F)"
apply clarsimp
apply (subgoal_tac "insert a F = F") apply fastsimp+
done


lemma setsum_single_impl_empty [rule_format]: 
  "finite A \<Longrightarrow>  setsum (single \<circ> f) A = {#} \<longrightarrow> A = {}"
by (induct rule: finite.induct)
   (clarsimp simp add: setsum_insert_split split add: split_if_asm)+

lemma setsum_single_empty [simp]: "finite A \<Longrightarrow> 
  (setsum (single \<circ> f) A = {#}) = (A = {})"
apply (rule iffI)
apply (simp add: setsum_single_impl_empty)
apply simp
done


lemma melem_setsum_single [rule_format]:
  "finite A \<Longrightarrow> \<forall> x \<in> A. g x \<in># (setsum (single \<circ> g) A)"
by (induct rule: finite.induct)
   (simp add: setsum_insert_split)+

lemma setsum_single_impl_ex [rule_format]: "finite A \<Longrightarrow>
  k \<in># setsum (single \<circ> g) A \<longrightarrow> (\<exists>x\<in>A. k = g x)"
by (induct rule: finite.induct)
   (simp add: setsum_insert_split)+

lemma setsum_single_ex: "finite A \<Longrightarrow> 
  k \<in># (setsum (single \<circ> g) A) = (\<exists> x \<in> A. k = g x )"
apply (rule iffI)
apply (fast intro: setsum_single_impl_ex)
apply (fast intro: melem_setsum_single)
done

lemma setsum_Un_disjoint': "finite A ==> finite B
  ==> A Int B = {} ==> C = (A Un B) \<Longrightarrow> 
  setsum g C = setsum g A + setsum g B"
by (simp add: setsum_Un_disjoint)

lemma trans_pair_less [simp]: "trans pair_less"
  by (fastsimp simp add: pair_less_def)

lemma trans_mult [simp]: "trans (mult r)"
  by (simp add: mult_def)

lemma trans_mult_rule: "\<lbrakk> trans r; (x, y) \<in> mult r;
         (y, z) \<in> mult r \<rbrakk> \<Longrightarrow> (x, z) \<in> mult r"
  apply (insert trans_mult [of r])
  apply (unfold trans_def)
  apply blast
  done

lemma empty_mult1 [simp]:  "({#}, {#a#})  \<in> mult1 r"
by (simp add: mult1_def)

lemma empty_mult [simp]: "trans r \<Longrightarrow> J \<noteq> {#} \<Longrightarrow> ({#}, J)  \<in> mult r"
apply (subgoal_tac "({#} + {#}, {#} + J)  \<in> mult r")
apply simp
apply (rule one_step_implies_mult, assumption+)
apply fastsimp
done


lemma mult_not_less_empty_aux: "(K, L) \<in> mult r \<Longrightarrow> L \<noteq> {#}"
  apply (simp add: mult_def)
  apply (induct rule: trancl.induct)
  apply clarsimp+
  done

lemma mult_not_less_empty [simp]: "(K, {#}) \<notin> mult r"
  by (fastsimp dest: mult_not_less_empty_aux)


definition mult1_list :: "('a \<times> 'a) set => ('a list \<times> 'a list) set" 
  where "mult1_list r = inv_image (mult1 r) multiset_of"

definition mult_list :: "('a \<times> 'a) set => ('a list \<times> 'a list) set" 
  where "mult_list r = inv_image (mult r) multiset_of"

lemma wf_mult1_list: "wf r \<Longrightarrow> wf (mult1_list r)"
  by (fastsimp simp add: mult1_list_def intro: wf_mult1)

lemma wf_mult_list: "wf r \<Longrightarrow> wf (mult_list r)"
  by (fastsimp simp add: mult_list_def intro: wf_mult)

lemma mult1_list_hd : "(xs, x # xs) \<in> (mult1_list r)"
  apply (simp add: mult1_list_def mult1_def)
  apply (intro exI)
  apply (rule conjI)
  apply (rule refl)
  apply (rule_tac x="{#}" in exI)
  apply simp
  done

lemma trans_mult_list [simp]: "trans (mult_list r)"
  by (simp add: mult_list_def trans_inv_image)


lemma mult1_list_hd_replace [rule_format]: 
  "\<forall> n \<in> set ns. (n, x) \<in> r \<Longrightarrow> (ns @ xs, x # xs) \<in> (mult1_list r)"
  apply (simp add: mult1_list_def mult1_def)
  apply (intro exI)
  apply (rule conjI)
  apply (rule refl)
  apply (intro exI conjI)
  apply (rule trans) apply (rule union_commute) apply (rule refl)
  apply (clarsimp simp add: set_count_greater_0)
  done


lemma mult_list_sublist: 
  "trans r \<Longrightarrow> 
  multiset_of pre + multiset_of post \<noteq> {#} \<Longrightarrow> 
  (xs, pre @ xs @ post) \<in> (mult_list r)"
  apply (simp add: mult_list_def)
  apply (subgoal_tac 
    "(multiset_of xs + {#}, multiset_of xs + (multiset_of pre + multiset_of post)) \<in> mult r")
  apply simp
  apply (subgoal_tac "multiset_of pre + (multiset_of xs + multiset_of post)
    = multiset_of xs + (multiset_of pre + multiset_of post)")
  apply simp
  apply (simp add: union_assoc [THEN sym] del: union_assoc)
  apply (rule union_commute)
  apply (erule one_step_implies_mult)
  apply simp+
  done

lemma one_step_mult_combined: "trans r ==> (K, J)  \<in> mult r
  ==> (I + K, I + J) \<in> mult r"
  apply (frule mult_implies_one_step) apply assumption
  apply (clarsimp simp add: union_assoc [THEN sym])
  apply (rule one_step_implies_mult)
  apply assumption+
  done


lemma one_step_mult_combined2: "trans r ==> (K, J)  \<in> mult r \<Longrightarrow> 
  (I, L)  \<in> mult r
  ==> (I + K, L + J) \<in> mult r"
  apply (rule trans_mult_rule [where y="I+J"]) apply assumption
  apply (rule one_step_mult_combined) apply assumption+
  apply (subgoal_tac "I + J = J + I")
  apply (subgoal_tac "L + J = J + L")
  apply simp
  apply (rule one_step_mult_combined) apply assumption+
  apply (rule union_commute)+
  done

definition mult_reflcl :: "('a \<times> 'a) set => ('a multiset \<times> 'a multiset) set" where
  "mult_reflcl r = (mult r)^="


lemma one_step_mult_combined3: "trans r ==> 
  (I, L)  \<in> mult_reflcl r \<Longrightarrow> 
  (K, J)  \<in> mult r \<Longrightarrow> 
  J \<noteq> {#} ==>
  (I + K, L + J) \<in> mult r"
  apply (simp add: mult_reflcl_def)
  apply (elim disjE)

    (* case (I, L) \<in> mult1 r *)
  apply (rule trans_mult_rule [where y="I+J"]) apply assumption
  apply (rule one_step_mult_combined) apply assumption+
  apply (insert union_commute [of I J])
  apply (insert union_commute [of L J])
  apply simp
  apply (rule one_step_mult_combined) apply assumption+

    (* case I = L *)
  apply (fastsimp intro: one_step_mult_combined) 
  done




lemma [simp]: "(x,x) \<in> pair_leq"
  by (simp add: pair_leq_def)

lemma pair_leq_0_0 [simp]: " ((0, 0), (x, y)) \<in> pair_leq"
  by (simp add: pair_leq_def) (fast intro: pair_lessI1 pair_lessI2)+


lemma mult1_singleton_decomp:
  "((M, {# y #}) \<in> mult1 r) = (\<forall> x. x \<in>#  M \<longrightarrow> ((x, y) \<in> r))"
apply (simp add: mult1_def)
apply (rule iffI)
apply (clarsimp simp add: single_is_union)
apply (rule_tac x=y in exI)
apply (rule_tac x="{#}" in exI)
apply simp
done


lemma mult_singleton_decomp:
  "trans r \<Longrightarrow> 
  ((M, {# y #}) \<in> mult r) = 
  (\<forall> x. x \<in>#  M \<longrightarrow>((x, y) \<in> r))"
apply (rule iffI)
apply (frule mult_implies_one_step) apply assumption
apply (clarsimp simp add: single_is_union)

apply (simp add: mult_def)
apply (rule r_into_trancl)
apply (simp add: mult1_singleton_decomp)
done


lemma mult_singletons [simp]: 
  "trans r \<Longrightarrow> (({# x #}, {# y #}) \<in> mult r) = ((x, y) \<in> r)"
by (simp add: mult_singleton_decomp)

lemma mult_multiset_sum_singleton_decomp: 
  "trans r 
  \<Longrightarrow> ((a + b), {# y #}) \<in> mult r =
  ((a, {# y #}) \<in> mult r  \<and> (b, {# y #}) \<in> mult r)"
apply (case_tac "a = {#}")
apply simp
apply (case_tac "b = {#}")
apply simp
apply (fastsimp simp add: mult_singleton_decomp)
done

  (* --------------------------------------------------  *)
  (* Measures for aboxes *)
  (* --------------------------------------------------  *)


fun sizeC ::" ('nr, 'nc) concept \<Rightarrow> nat"
  where
  "sizeC  (AtomC a) = 1"
  |"sizeC Top   =  1"
  |"sizeC Bottom  = 1"
  |"sizeC (NotC  c1) =  1 +  (sizeC c1)"
  |"sizeC (AndC  c1 c2) = 1 +  (sizeC c1) + (sizeC c2)"
  |"sizeC (OrC  c1 c2) = 1+  (sizeC c1) + (sizeC c2)"
  |"sizeC (AllC r c1) = 1+  (sizeC c1) "
  |"sizeC (SomeC  r c1) = 1+ (sizeC c1) "


    (*********** Or Applicable **********************)

inductive or_applicable  :: "(('ni,'nr,'nc) abox) \<Rightarrow> ('ni,'nr,'nc) fact \<Rightarrow> bool" 
  where
  App_or :
  "\<lbrakk> Inst x (OrC c1 c2) = f  ;  f \<in>AB  ;  
  (Inst x c1) \<notin> AB  ;  (Inst x c2 ) \<notin> AB \<rbrakk> \<Longrightarrow>
  or_applicable AB f"

lemma or_app_orright_rule1 :
  " Orruleright AB AB2  \<Longrightarrow> \<exists> f. or_applicable AB f"
  apply (clarsimp simp  add: orruleright_simp)
  apply (fast intro: App_or) 
  done

lemma or_app_orleft_rule1 :
  " Orruleleft AB AB2  \<Longrightarrow> \<exists> f. or_applicable AB f"
  apply (clarsimp simp  add: orruleleft_simp)
  apply (fast intro: App_or) 
  done

lemma or_app_orright_rule :
  "or_applicable AB f \<Longrightarrow>( \<exists> AB2. Orruleright AB AB2) "
  apply (induct rule: or_applicable.induct)
  apply (rule_tac x = " ( insert (Inst x c2) AB  )" in exI)
  apply (fastsimp simp add: orruleright_simp )
  done

lemma or_app_orleft_rule :
  "or_applicable AB f \<Longrightarrow>( \<exists> AB2. Orruleleft AB AB2) "
  apply (induct rule: or_applicable.induct)
  apply (rule_tac x = " ( insert (Inst x c1) AB  )" in exI)
  apply (fastsimp simp add: orruleleft_simp )
  done


    (*************Some *********************)

inductive some_applicable :: "(('ni,'nr,'nc) abox) \<Rightarrow> ('ni,'nr,'nc) fact \<Rightarrow> bool" 
  where
  App_some :
  "\<lbrakk>  f= ( Inst x (SomeC  r c1)) ; f \<in> AB ; 
  \<forall> y. \<not>  ((Rel r x y )\<in>AB  \<and>  (Inst y c1 )\<in>AB) \<rbrakk> \<Longrightarrow>
  some_applicable AB f"

inductive some_applicable_2 :: "(('ni,'nr,'nc) abox) \<Rightarrow> ('ni,'nr,'nc) fact \<Rightarrow> bool" 
  where
  App_some2 :
  "\<lbrakk>f= ( Inst x (SomeC  r c1)) ; 
  \<forall> y. \<not>  ((Rel r x y )\<in>AB  \<and>  (Inst y c1 )\<in>AB) \<rbrakk> \<Longrightarrow>
  some_applicable_2 AB f"


lemma some_app_some_rule1 :
  " Somerule3 AB AB2  \<Longrightarrow> \<exists> f. some_applicable AB f"
  apply (clarsimp simp  add: somerule3_simp)
  apply (rule_tac x = " ( Inst x (SomeC r c1) )" in exI)
  apply (fast intro: App_some) 
  done


lemma some_app_some_rule :
  "some_applicable AB f \<Longrightarrow>( \<exists> AB2. Somerule3 AB AB2) "
  apply (induct rule: some_applicable.induct)
  apply (rule_tac x = " (\<lambda> z.  insert (Rel r x z) (insert (Inst z c1) AB)) (SOME b.(not_occurs_ni_in_abox b AB) )" in exI)
  apply (fastsimp simp add: somerule3_simp  )
  done

    (*******************************************************)
    (************compute the measure ***********************)

fun set_y_c_in_abox:: " ('nr, 'nc) concept \<Rightarrow> ('ni,'nr,'nc) abox  \<Rightarrow> 'ni set"
  where
  " set_y_c_in_abox  c Ab = { x. (Inst x c) \<in> Ab } "

fun  set_y_xry_in_abox  :: " 'ni \<Rightarrow> 'nr role \<Rightarrow> ('ni,'nr,'nc) abox  \<Rightarrow> 'ni set"
  where
  "set_y_xry_in_abox x r Ab  = { y. (Rel r x y )\<in> Ab}"

fun comp11 ::"'ni \<Rightarrow>('nr, 'nc) concept \<Rightarrow>  'nr role \<Rightarrow> ('ni,'nr,'nc) abox  \<Rightarrow> nat"
  where 
  "comp11 x c r Ab = card( (set_y_xry_in_abox x r Ab) -(set_y_c_in_abox  c Ab)) "


  (**********************************************************)
  (*         Nember of exist term in Abox                   *)
  (**********************************************************)
fun some_term :: " 'ni \<Rightarrow> 'nr role \<Rightarrow> ('nr,'nc) concept \<Rightarrow>  ('ni,'nr,'nc) abox " 
  where 
  "some_term x r (AtomC  a)  = {}"
  |"some_term x r Top   =   {}"
  |"some_term x r Bottom  = {}"
  |"some_term x r (NotC  c1) =  (some_term  x r  c1) "
  |"some_term x r (AndC  c1 c2) =(some_term  x r c1) \<union>    ( some_term  x r c2)"
  |"some_term x r (OrC  c1 c2) =  (some_term x r c1) \<union>  ( some_term  x  r c2)"
  |"some_term x r  (AllC  r1 c1) = some_term  x r c1 "
  | "some_term x r ( SomeC  r1 c1) = (if (r=r1) then (insert (Inst x (SomeC r1 c1)) (some_term  x r c1) ) else (some_term  x r  c1) ) "

fun  set_some_in_fact :: " 'ni \<Rightarrow> 'nr role \<Rightarrow> ('ni,'nr,'nc) fact \<Rightarrow>  ('ni,'nr,'nc) abox "   
  where 
  "set_some_in_fact  x  r   (Inst  y c)    = some_term  x  r c"   
  |"set_some_in_fact  x  r  (Rel r1 x1 y1)  =  {} "

  (* changed fun ... where to constdefs *)
constdefs
  set_some_in_abox :: " 'ni \<Rightarrow> 'nr role \<Rightarrow> ('ni,'nr,'nc) abox \<Rightarrow> (('ni,'nr,'nc) abox)"   
  "set_some_in_abox x  r Ab \<equiv> \<Union>  (set_some_in_fact x  r)`Ab " (*" {y. �f�Ab.  ( y = (set_some_in_fact x  r f))} "*)


inductive some_applicable_3:: "(('ni,'nr,'nc) abox) \<Rightarrow> ('ni,'nr,'nc) fact  \<Rightarrow> bool" 
  where
  App_some3 :
  "\<lbrakk>f= ( Inst x (SomeC  r c1)) ; \<forall>  y. \<not>  ((Rel r x y )\<in> AB  \<and>   (Inst y c1 )\<in> AB) \<rbrakk> \<Longrightarrow>
  some_applicable_3 AB f"

  (* TODO: rewrite some_applicable_2 *)
(*consts some_applicable2 :: "('ni,'nr,'nc) abox \<Rightarrow> ('ni,'nr,'nc) abox"*)
constdefs some_applicable2 :: "('ni,'nr,'nc) abox \<Rightarrow> ('ni,'nr,'nc) abox"
" some_applicable2 ab  \<equiv> {f. (\<exists> x  c1 r. f= (Inst x (SomeC r c1 ))  \<and> (\<forall> y.
                      ~ ((Rel r x y ) \<in> ab \<and>  (Inst y c1 ) \<in> ab) ) )} "
  (* Thats the way some_applicable_2 should work. To be removed !!! *)
lemma somerule2_simp :
" some_applicable_3 b f = (\<exists> x  c1 r. f= (Inst x (SomeC r c1 ))  \<and> (\<forall> y.
                      ~ ((Rel r x y ) \<in> b \<and>  (Inst y c1 ) \<in> b) ) )"
  apply (rule iffI)
  apply (induct rule: some_applicable_3.induct)
  apply fast
  apply (fast intro: App_some3)
  done

lemma flabs1: "some_applicable_3 AB f = (f \<in> some_applicable2 AB)"
by (clarsimp simp add: somerule2_simp some_applicable2_def)


constdefs set_some :: 
  "'ni \<Rightarrow> 'nr role \<Rightarrow> ('ni,'nr,'nc) abox \<Rightarrow>  (('ni,'nr,'nc) abox)"
  "set_some x r ab \<equiv> ((set_some_in_abox x  r ab ) \<inter> (some_applicable2 ab))"

lemma set_some_in_abox_mono: "ab \<subseteq> ab' \<Longrightarrow>
  set_some_in_abox x r ab \<subseteq> set_some_in_abox x r ab'"
by (fastsimp simp add: set_some_in_abox_def)

  (* TODO: prove after redefinition *)
axioms  some_applicable2_mono: "ab \<subseteq> ab' \<Longrightarrow>
  some_applicable2 ab \<subseteq> some_applicable2 ab'"
(*
apply ( clarsimp simp add: some_applicable2_def) 
 apply (drule_tac x="y" in spec)
apply auto
apply (clarsimp simp add: subset_iff_psubset_eq)
apply (elim disjE)apply (frule psubset_imp_ex_mem)
apply blast
apply auto apply (clarsimp simp add :psubset_imp_ex_mem)
sorry
*)
lemma set_some_mono: "ab \<subseteq> ab' \<Longrightarrow>
  set_some x r ab \<subseteq> set_some x r ab'"
by (unfold set_some_def)
   (blast dest: set_some_in_abox_mono some_applicable2_mono)


(* changed fun ... where to constdefs *)
constdefs
  comp12 ::" 'ni  \<Rightarrow> 'nr role  \<Rightarrow> ('ni,'nr,'nc) abox  \<Rightarrow> nat "
  "comp12 x r ab \<equiv> card (set_some x r ab)"


lemma finite_set_some_term [simp]: "finite (some_term x r c)"
by (induct c) auto

lemma finite_set_some_in_fact [simp]: "finite (set_some_in_fact x r f)"
by (case_tac f) simp_all

lemma finite_set_some [simp]: "finite ab \<Longrightarrow> finite (set_some x r ab)"
by (simp add : set_some_def set_some_in_abox_def)


lemma comp12_mono: "finite ab' \<Longrightarrow> ab \<subseteq> ab' \<Longrightarrow> 
  comp12 x r ab \<le> comp12 x r ab'"
apply (unfold comp12_def)
apply (rule card_mono)
apply (erule finite_set_some)
apply (erule set_some_mono)
done


axioms  comps_mono: "ab \<subseteq> ab' \<Longrightarrow> 
  ((n, comp11 x c r ab' + comp12 x r ab'),
   (n, comp11 x c r ab  + comp12 x r ab)) \<in> pair_leq"



  (* mes_comp of Termination.thy *)
constdefs meas_comp_set  ::  "('ni,'nr,'nc) abox \<Rightarrow> ('ni,'nr,'nc) fact \<Rightarrow> nat*nat"
  "meas_comp_set ab fct ==
       (case fct of 
          Inst x c \<Rightarrow> (case c of
             (AndC c1 c2) \<Rightarrow> if and_applicable ab fct then (sizeC c, 0) else (0,0)
           | (OrC c1 c2)  \<Rightarrow> if or_applicable ab fct then (sizeC c, 0) else (0,0)
           | (SomeC r c1) \<Rightarrow> if some_applicable ab fct then (sizeC c, 0) else (0,0)
           | (AllC r c1)  \<Rightarrow> (sizeC c , (comp11 x c1 r ab) + (comp12 x r ab))
           |_ \<Rightarrow>(0,0)
         )
        | _ \<Rightarrow> (0,0)
       )"

lemma meas_comp_bound:
  "sizeC c < m \<Longrightarrow> (meas_comp_set ab (Inst x c), (m, n)) \<in> pair_less"
  apply (simp add: meas_comp_set_def)
  apply (case_tac c)
  apply (simp add: pair_less_def)+
  done

constdefs multiset_of_abox :: "('ni,'nr,'nc) abox \<Rightarrow> (nat * nat) multiset"
  "multiset_of_abox ab \<equiv> setsum (single \<circ> (meas_comp_set ab)) ab"

constdefs measure_abox_order ::
  "(('ni, 'nr, 'nc) abox * ('ni, 'nr, 'nc) abox) set"
  "measure_abox_order \<equiv> 
  inv_image (mult pair_less) multiset_of_abox"

lemma wf_measure_abox_order: "wf measure_abox_order"
  by (simp add: measure_abox_order_def)
     (intro wf_inv_image wf_mult wf_pair_less)


constdefs pushing_new_facts :: "('ni, 'nr, 'nc) rule \<Rightarrow> bool"
  "pushing_new_facts r \<equiv>
  (\<forall> abx abx'. r abx abx' \<longrightarrow> abx \<subseteq> abx')"

(*
constdefs measure_decreasing_rule :: "('ni, 'nr, 'nc) rule \<Rightarrow> bool"
  "measure_decreasing_rule r \<equiv>
  (\<forall> abx abx' n. 
  r abx abx' \<longrightarrow> 
  n = abx' - abx \<longrightarrow>
  (\<exists> f \<in> abx.
  ((\<Sum>x\<in>n. {#meas_comp_set (n \<union> abx) x#}) +
              {#meas_comp_set (n \<union> abx) f#},
              {#meas_comp_set abx f#})
       \<in> mult pair_less))"
*)

constdefs measure_decreasing_rule :: "('ni, 'nr, 'nc) rule \<Rightarrow> bool"
  "measure_decreasing_rule r \<equiv>
  (\<forall> abx abx'. 
  r abx abx' \<longrightarrow> 
  (\<exists> f \<in> abx.
  ((\<Sum>x\<in> (abx' - abx). {#meas_comp_set abx' x#}) +
              {#meas_comp_set abx' f#},
              {#meas_comp_set abx f#})
       \<in> mult pair_less))"


lemma foo1: 
"finite abx \<Longrightarrow> f \<in> abx \<Longrightarrow> 
(\<Sum>x\<in>abx. {#meas_comp_set abx' x#}) =
 {#meas_comp_set abx' f#} +
  (\<Sum>x\<in>(abx - {f}). {#meas_comp_set abx' x#})"
by (insert setsum_diff1' [of abx f "single \<circ> (meas_comp_set abx')"])
  simp


lemma foo2: "trans r \<Longrightarrow> 
  finite A \<Longrightarrow>
  \<forall> x \<in> A. (g x, h x) \<in> reflcl r \<Longrightarrow>
  (setsum (single \<circ> g) A, setsum (single \<circ> h) A) \<in> mult_reflcl r"

apply (case_tac "{x \<in> A. g x \<noteq> h x} = {}")
apply (simp add: mult_reflcl_def)


apply (subgoal_tac "\<exists> E N I J K. 
  E = {x \<in> A. g x = h x} \<and> 
  N = {x \<in> A. g x \<noteq> h x} \<and> 
  I = setsum (single \<circ> g) E \<and>
  K = setsum (single \<circ> g) N \<and>
  J = setsum (single \<circ> h) N \<and>
  setsum (single \<circ> g) A = I + K \<and>
  setsum (single \<circ> h) A = I + J")

apply (clarsimp simp add: mult_reflcl_def)
apply (erule one_step_implies_mult)

apply (rule notI)
apply (fold comp_def)
apply (subgoal_tac "finite {x \<in> A. g x \<noteq> h x}") prefer 2 apply (fast intro: finite_subset)
apply (simp only: setsum_single_empty)

apply clarsimp

apply (fold comp_def)
apply (subgoal_tac "finite {x \<in> A. g x \<noteq> h x}") prefer 2 apply (fast intro: finite_subset)
apply (simp only: setsum_single_ex)
apply clarsimp
apply (rename_tac x z)
apply (rule_tac x="h z" in bexI) apply fast
apply simp
apply (fold comp_def)
apply (subgoal_tac "finite {x \<in> A. g x \<noteq> h x}") prefer 2 apply (fast intro: finite_subset)
apply (simp only: setsum_single_ex)
apply fast

  (* subgoal \<exists> E N I J K.  ... *)
apply (intro exI)
apply (rule conjI, rule refl)+

apply (rule conjI) 
apply (fast intro: setsum_Un_disjoint' finite_subset)

apply (subgoal_tac "setsum (single \<circ> g) {x \<in> A. g x = h x} =
setsum (single \<circ> h) {x \<in> A. g x = h x}")
  prefer 2 apply (simp add: setsum_def)
apply (simp only:)
apply (fast intro: setsum_Un_disjoint' finite_subset)
done

(*
lemma meas_comp_antimono: 
  "set ab \<subseteq> set ab' \<Longrightarrow> 
  ((meas_comp ab' fct), (meas_comp ab fct)) \<in> pair_leq"
  apply (simp add: meas_comp_def split add: fact.split concept.split)
  apply (intro allI impI conjI)
  apply (fast dest: appcond_and_antimono)
  apply (fast dest: appcond_or_antimono)
  apply (erule comps_mono)
  apply (fast dest: appcond_some_antimono)
  done
*)

lemma meas_comp_set_antimono: 
  "ab \<subseteq> ab' \<Longrightarrow> 
  ((meas_comp_set ab' fct), (meas_comp_set ab fct)) \<in> pair_leq"
sorry


lemma rearrange_foo2 : "a + b + c = b + (c + (a::'a multiset))"
sorry

lemma measure_abox_order_decreasing: "
  finite abx' \<Longrightarrow>
  r abx abx'
  \<Longrightarrow> pushing_new_facts r
  \<Longrightarrow> measure_decreasing_rule r
  \<Longrightarrow> (abx', abx) \<in> measure_abox_order"
  apply (clarsimp simp add: pushing_new_facts_def)
  apply (drule spec)+ apply (drule mp, assumption)
  apply (subgoal_tac "finite abx") prefer 2 apply (erule finite_subset, assumption)

apply (unfold measure_decreasing_rule_def)
apply (drule spec)+
apply (drule mp, assumption)
apply clarsimp
  
  apply (rename_tac f)

  apply (unfold measure_abox_order_def)
  apply (simp add: inv_image_def)
  apply (simp add: multiset_of_abox_def)

apply (subgoal_tac "(\<Sum>x\<in>abx'. {#meas_comp_set abx' x#}) =
  (\<Sum>x\<in>(abx \<union> (abx' - abx)). {#meas_comp_set abx' x#})")
 prefer 2 apply (subgoal_tac "(abx \<union> (abx' - abx)) = abx'") apply simp apply blast

apply (subgoal_tac "abx \<inter> (abx' - abx) = {}") prefer 2 apply blast
apply (subgoal_tac "finite (abx' - abx)") prefer 2 apply (erule finite_Diff)
apply (simp only: setsum_Un_disjoint)

apply (subgoal_tac "(\<Sum>x\<in>abx. {#meas_comp_set abx' x#}) =
  {#meas_comp_set abx' f#} +
  (\<Sum>x\<in>(abx - {f}). {#meas_comp_set abx' x#})")
prefer 2 apply (fast intro: foo1)

apply (subgoal_tac "(\<Sum>x\<in>abx. {#meas_comp_set abx x#}) =
  {#meas_comp_set abx f#} +(\<Sum>x\<in>(abx - {f}). {#meas_comp_set abx x#})")
prefer 2 apply (fast intro: foo1)
apply (simp only:)

apply (subgoal_tac "({#meas_comp_set abx' f#} + (\<Sum>x\<in>abx - {f}. {#meas_comp_set abx' x#}) +
            (\<Sum>x\<in>abx' - abx. {#meas_comp_set abx' x#}))
= (\<Sum>x\<in>abx - {f}. {#meas_comp_set abx' x#})
+ ((\<Sum>x\<in>abx' - abx. {#meas_comp_set abx' x#}) + {#meas_comp_set abx' f#})")
prefer 2 apply (rule rearrange_foo2)



apply (subgoal_tac "{#meas_comp_set abx f#} + (\<Sum>x\<in>abx - {f}. {#meas_comp_set abx x#}) = (\<Sum>x\<in>abx - {f}. {#meas_comp_set abx x#}) + {#meas_comp_set abx f#}")
prefer 2 apply (rule union_commute)

apply (simp only:)

  apply (rule one_step_mult_combined3) apply simp

defer

apply simp
apply simp

apply (fold comp_def)
apply (rule foo2) apply simp apply (fast intro: finite_subset)
apply (fold pair_leq_def)
apply (fast intro: meas_comp_set_antimono)
done


lemma pushing_new_facts_Andrule: 
  "pushing_new_facts Andrule"
by (clarsimp simp add: pushing_new_facts_def andrule_simp)


lemma meas_comp_AndC:
  "and_applicable abx (Inst x (AndC c1 c2)) \<Longrightarrow>
  meas_comp_set abx (Inst x (AndC c1 c2)) = (Suc (sizeC c1 + sizeC c2), 0)"
by (simp add: meas_comp_set_def)



lemma measure_decreasing_Andrule:
 "measure_decreasing_rule Andrule"
  apply (unfold measure_decreasing_rule_def)
  apply (clarsimp simp add: andrule_simp)
  apply (rule bexI) prefer 2 apply (fastsimp simp add: and_applicable_def)
  apply (simp add: mult_multiset_sum_singleton_decomp
    setsum_insert_split insert_Diff_if meas_comp_bound meas_comp_AndC)
  apply (simp add: meas_comp_set_def pair_less_def and_applicable_def)
done


lemma finite_preserving_Andrule:
  "finite abx \<Longrightarrow> Andrule abx n \<Longrightarrow> finite n"
by (clarsimp simp add: andrule_simp)

lemma measure_abox_order_Andrule: 
  "finite abx \<Longrightarrow> 
  Andrule abx n \<Longrightarrow> (n, abx) \<in> measure_abox_order"
apply (rule measure_abox_order_decreasing [where r=Andrule])
apply (fast intro: finite_preserving_Andrule)
apply assumption
apply (rule pushing_new_facts_Andrule)
apply (fast intro: measure_decreasing_Andrule)
done


(**** ALC rules ****)
lemma alc_rule_impl_measure_abox_order:
  "finite abx \<Longrightarrow>
  (alc_rule abx n) \<Longrightarrow> (n, abx) \<in> measure_abox_order"
  apply (simp add: alc_rule_def list_alc_rules_def)
  apply (elim disjE)
  apply (fast elim: measure_abox_order_Andrule)
(*
  apply (fast elim: measure_abox_order_or_rule)
  apply (fast elim: measure_abox_order_all_rule)
apply (fast elim: measure_abox_order_some_rule)
done
*)
sorry

end
