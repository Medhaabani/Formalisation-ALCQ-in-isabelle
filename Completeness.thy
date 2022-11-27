theory Completeness imports Tableau
begin
(************************ completenss **********************************)
text{* an abox is complete if no rule is applied *}

  (* the following should not be called "complete", but rather "saturated". *)
fun complete :: "('ni,'nr,'nc) abox \<Rightarrow> bool"
  where 
  "complete AB1 = (\<forall> AB2. \<not> (alc_rule AB1 AB2))"

  (* the following should be called complete *)
constdefs
  cmplt :: "('ni,'nr,'nc) rule \<Rightarrow> bool"
  "cmplt r == \<forall> A1. satisfiable_abox A1 \<longrightarrow> (\<exists> A2. r A1 A2)
  \<longrightarrow> (\<exists> A2. r A1 A2 \<and> satisfiable_abox A2)"


lemma and_cmplt [simp]: "cmplt Andrule"
apply (clarsimp simp add: cmplt_def andrule_simp satisfiable_abox_def)
apply (intro exI conjI)
apply assumption
apply (rule refl)
apply (fastsimp simp add: and_applicable_def)
done

lemma satisfiable_fact_Inst_OrC:
  "\<lbrakk>Inst x (OrC c1 c2) \<in> A1; \<forall>f\<in>A1. satisfiable_fact (ii, icr) f \<rbrakk>
\<Longrightarrow> satisfiable_fact (ii, icr) (Inst x c1) \<or> satisfiable_fact (ii, icr) (Inst x c2)"
by (drule_tac x="Inst x (OrC c1 c2)" in bspec) simp+

  (* the following result does not hold for Orruleleft or Orruleright alone *)
lemma or_cmplt [simp]: "cmplt Orrule"
apply (clarsimp simp add: cmplt_def orrule_simp satisfiable_abox_def)
apply (frule satisfiable_fact_Inst_OrC)
apply assumption
apply blast
done

lemma satisfiable_fact_Inst_SomeC:
  "\<lbrakk>Inst x (SomeC r c) \<in> A1; 
  (ii x, y) \<in> interpR icr r; y \<in> interpC icr c;
  \<forall>f\<in>A1. \<not> occurs_ni_in_fact z f
 \<rbrakk>
\<Longrightarrow> satisfiable_fact (ii(z:=y), icr) (Rel r x z)
  \<and> satisfiable_fact (ii(z:=y), icr) (Inst z c)"
by fastsimp

lemma satisfiable_fact_interp_upd [rule_format, simp]:
  "\<not> occurs_ni_in_fact z f 
       \<longrightarrow> satisfiable_fact (ii(z := y), icr) f = satisfiable_fact (ii, icr) f"
by (case_tac f) simp+

lemma some_cmplt [simp]: "cmplt Somerule"
apply (clarsimp simp add: cmplt_def somerule_simp satisfiable_abox_def)
apply (rename_tac A1 ii icr x z c1 r)
apply (frule_tac x="Inst x (SomeC r c1)" in bspec) apply assumption
apply clarsimp
apply (frule satisfiable_fact_Inst_SomeC)
apply assumption+
apply (intro exI conjI)
apply assumption+
apply (rule refl)
apply (clarsimp simp del: satisfiable_fact.simps)
apply (rule conjI, assumption)+
apply simp
done

lemma some_gen_cmplt [simp]: 
  "\<forall> ab. not_occurs_ni_in_abox (gen ab) ab
  \<Longrightarrow> cmplt (Somerule_gen gen)"
apply (clarsimp simp add: cmplt_def somerule_gen_simp satisfiable_abox_def)
apply (rename_tac A1 ii icr x c1 r)
apply (frule_tac x="Inst x (SomeC r c1)" in bspec) apply assumption
apply clarsimp
apply (frule satisfiable_fact_Inst_SomeC)
apply assumption+
apply fast
apply (intro exI conjI)
apply assumption+
apply (rule refl)
apply (clarsimp simp del: satisfiable_fact.simps)
apply (rule conjI, assumption)+
apply simp
done

lemma all_cmplt [simp]: "cmplt Allrule"
apply (clarsimp simp add: cmplt_def allrule_simp satisfiable_abox_def)
apply (intro exI conjI)
apply assumption+
apply (rule refl)
apply (clarsimp simp del: satisfiable_fact.simps)
apply (rule conjI)
prefer 2 apply assumption
apply (rename_tac A1 a b x y r c1)
apply (frule_tac x="Inst x (AllC r c1)" in bspec)
apply assumption
apply (drule_tac x="Rel r x y" in bspec)
apply assumption
apply simp
done


fun contains_clash :: " ('ni,'nr,'nc) abox \<Rightarrow> bool  "
  where
  " contains_clash AB = (\<exists> x c. ((Inst x c) \<in> AB \<and> (Inst x (NotC c)) \<in> AB) \<or> ((Inst x Bottom) \<in> AB))"

lemma sat_xc_notsat_notxc : 
  "satisfiable_fact (a, b) (Inst x c) = (\<not> (satisfiable_fact (a, b) (Inst x (NotC c))))"
  by simp

    (* 
    lemma "\<lbrakk>\<forall> x. Q x; \<forall> y. R y \<rbrakk> \<Longrightarrow> A "
    thm spec
    apply (drule_tac P=R  in spec)
    apply (drule spec)
    *)

lemma content_clash_not_satisfiable  :
  " \<lbrakk>contains_clash AB ; satisfiable_abox AB\<rbrakk> \<Longrightarrow> False"
  apply ( clarsimp simp add: satisfiable_abox_def)
  apply (elim disjE exE conjE)
  thm spec			
    (* \<lbrakk>\<forall>x\<in>?A. ?P x; ?x \<in> ?A\<rbrakk> \<Longrightarrow> ?P ?x  *)
  thm bspec [where x="Inst x c" and P="satisfiable_fact (a, b)" and A = AB]
    (* 
    \<lbrakk>\<forall>x\<in>AB. satisfiable_fact (a, b) x; Inst x c \<in> AB\<rbrakk> \<Longrightarrow> satisfiable_fact (a, b) (Inst x c)
    *)
  apply (frule_tac x="Inst x c" and P="satisfiable_fact (a, b)" in  bspec) apply assumption
  apply (frule_tac x="Inst x (NotC c)" in  bspec) apply assumption
  apply fastsimp+
  done

lemma content_clash_not_satisfiable2  :
  " \<lbrakk>contains_clash AB \<rbrakk> \<Longrightarrow> \<not>  satisfiable_abox AB "
  apply (rule notI)
  apply (fast intro: content_clash_not_satisfiable)
  done
    (* 
    apply (clarsimp simp add : satisfiable_abox_def)
    apply (simp only: ball_simps [THEN sym])
    thm bexI
    apply (elim disjE exE conjE)
    apply (rule_tac  x="Inst x c" in bexI)
    *)

    (**************************************************)
text{*  interpretation  canonique  *}

fun set_ni_in_abox :: "  ('ni,'nr,'nc) abox \<Rightarrow> 'ni set"   
  where 
  " set_ni_in_abox  ab ={ x. \<exists> f \<in> ab. (occurs_ni_in_fact x f)} "

  (* lemma  example1 :
  "  set_ni_in_abox {(Diff 0 1), (Rel (AtomR 3) 1 2)} ={0,1,2} "
  by auto *)

lemma tow_spec_the_same:
  "set_ni_in_abox b1 = set_ni_in_abox1 b1"
  by auto

fun int_set_ni :: "'ni Interp_inst\<Rightarrow> 'ni set \<Rightarrow> domtype set "
  where
  "int_set_ni ii setni = {y .\<exists> x \<in> setni . y = (ii x)} "

lemma "int_set_ni ii setni = ii` setni"
  by (simp add: image_def)

fun int_set_paire_ni :: "'ni Interp_inst\<Rightarrow> ('ni* 'ni) set \<Rightarrow> (domtype * domtype) set "
  where
  "int_set_paire_ni ii setpaireni = {(y1,y2) .\<exists> (x1, x2) \<in> setpaireni . (y1, y2) = (ii x1, ii x2)} "

lemma "int_set_paire_ni ii setpaireni = (\<lambda> (x1, x2). (ii x1, ii x2)) ` setpaireni"
  apply (simp add: image_def split_def)
  apply (rule Collect_cong)
  apply (rule iffI)
  apply clarsimp
  apply (rule  bexI) prefer 2 apply assumption apply simp
  apply clarsimp
  apply (rule  bexI) prefer 2 apply assumption apply simp
  done

    (* domaine*)
definition  mysetdomaine ::"'ni Interp_inst \<Rightarrow>  ('ni,'nr,'nc) abox \<Rightarrow>domtype set "
  where  
  "mysetdomaine ii AB =  ii` (set_ni_in_abox AB)"

definition interp_atom_A_in_AB ::" 'nc \<Rightarrow>  ('ni,'nr,'nc) abox \<Rightarrow> 'ni set"
  where
  "interp_atom_A_in_AB A AB = {x. (Inst x (AtomC A)) \<in> AB }"

definition interp_atom_A_in_AB_dom :: "'ni Interp_inst \<Rightarrow> 'nc \<Rightarrow>  ('ni,'nr,'nc) abox \<Rightarrow>domtype set "
  where
  " interp_atom_A_in_AB_dom ii A AB =  ii` (interp_atom_A_in_AB A AB)" 

definition rel_ni_atom_role :: " 'nr \<Rightarrow>  ('ni,'nr,'nc) abox \<Rightarrow> ('ni * 'ni) set"
  where 
  "  rel_ni_atom_role r AB = { (x, y) .   (Rel (AtomR r) x y) \<in>  AB}"

definition rel_ni_atom_role_dom :: "'ni Interp_inst \<Rightarrow> 'nr \<Rightarrow>  ('ni,'nr,'nc) abox \<Rightarrow>(domtype * domtype) set "
  where 
  "  rel_ni_atom_role_dom ii r AB = int_set_paire_ni ii (rel_ni_atom_role r AB )"

  (* problem of type ni et domtype *)

definition   can_in :: "'ni Interp_inst \<Rightarrow>('ni,'nr,'nc) abox  \<Rightarrow> ('nr,'nc)Interp "
  where
  " can_in ii AB  \<equiv> \<lparr>  domaine   = (mysetdomaine ii AB) ,
                       interp_c  = \<lambda> c.( interp_atom_A_in_AB_dom ii c AB), 
                       interp_r  = \<lambda> r. rel_ni_atom_role_dom ii r AB
                    \<rparr>"

  (********* proofs****************)
lemma can_in_satis_atom :
  "\<lbrakk> (Inst x (AtomC A)) \<in> AB \<rbrakk> \<Longrightarrow> satisfiable_fact (i, (can_in i AB)) (Inst x (AtomC A))"
  by (fastsimp  simp add: can_in_def interp_atom_A_in_AB_dom_def interp_atom_A_in_AB_def)

lemma can_int_sat_rel :
  "\<lbrakk> (Rel r x y) \<in> AB \<rbrakk> \<Longrightarrow> satisfiable_fact (i, (can_in i AB)) (Rel r x y)"
  apply (induct r)
  apply (fastsimp simp add: can_in_def rel_ni_atom_role_dom_def  rel_ni_atom_role_def)
  done

lemma notc_normal_abox :
  "\<lbrakk> is_Normal_Abox AB; Inst x (NotC c) \<in> AB \<rbrakk> \<Longrightarrow> \<exists> a.  c = AtomC a "
  apply (simp add:is_Normal_Abox_def) 
  apply (drule_tac x = "Inst x (NotC c) " in spec)
  apply simp
  done

lemma completl_cn_and :
  "\<lbrakk> complete  AB ;  (Inst x  (AndC c1 c2) ) \<in>  AB \<rbrakk> 
  \<Longrightarrow>  (Inst x  c1 ) \<in>  AB \<and>  (Inst x  c2 )  \<in> AB"
  apply (simp add : alc_rule_def list_alc_rules_def)
  apply (drule_tac x="insert (Inst x c2) (insert (Inst x c1) AB)" in  spec)
  apply (fastsimp simp add: andrule_simp and_applicable_def)
  done

lemma completl_cn_or :
  "  \<lbrakk> complete  AB ; Inst x (OrC c1 c2) \<in> AB \<rbrakk> \<Longrightarrow>
  (Inst x  c1 ) \<in>  AB \<or> (Inst x c2 ) \<in> AB "
  by (auto simp add : alc_rule_def list_alc_rules_def orruleleft_simp )

lemma can_in_satis_Top :
  "\<lbrakk> (Inst x Top) \<in> AB \<rbrakk> \<Longrightarrow> satisfiable_fact (i, (can_in i AB)) (Inst x Top)"
  by simp

lemma  completl_cn_all: 
  " \<lbrakk>complete  AB  ; Inst x (AllC r c) \<in> AB \<rbrakk>  \<Longrightarrow> \<forall>y. ((Rel r x y) \<in> AB  \<longrightarrow> (Inst y c) \<in> AB)"
  apply (rule allI )
  apply (clarsimp simp add : alc_rule_def list_alc_rules_def )
  apply (drule_tac x=" (insert (Inst y c) AB)" in  spec)
  apply (elim conjE )
  apply (fast intro: mk_Allrule) 
  done
lemma tt :
  " (\<forall>AB2 x c1 r.
        Inst x (SomeC r c1) \<in> AB \<longrightarrow>
        (\<exists>y. Rel r x y \<in> AB \<and> Inst y c1 \<in> AB) \<or>
        AB2 \<noteq> insert (Rel r x (SOME b. \<forall>f\<in>AB. \<not> occurs_ni_in_fact b f)) (insert (Inst (SOME b. \<forall>f\<in>AB. \<not> occurs_ni_in_fact b f) c1) AB))
=
(\<forall> x c1 r.
        Inst x (SomeC r c1) \<in> AB \<longrightarrow>
        (\<exists>y. Rel r x y \<in> AB \<and> Inst y c1 \<in> AB) \<or>
       (\<forall> AB2. AB2 \<noteq> insert (Rel r x (SOME b. \<forall>f\<in>AB. \<not> occurs_ni_in_fact b f)) (insert (Inst (SOME b. \<forall>f\<in>AB. \<not> occurs_ni_in_fact b f) c1) AB)))"
  by blast

lemma completl_cn_some0:
  " \<lbrakk>Inst x (SomeC r c) \<in> AB; \<forall>AB2. \<not> Somerule3 AB AB2\<rbrakk> \<Longrightarrow> \<exists>y. Rel r x y \<in> AB \<and> Inst y c \<in> AB"
  apply ( simp add :somerule3_simp)
  apply (simp add:tt )
  apply (drule_tac x = " x " in spec)
  apply (drule_tac x = " c " in spec)
  apply (drule_tac x = " r " in spec)
  apply simp
  apply auto
  done

lemma completl_cn_some:
  " \<lbrakk>Inst x (SomeC r c) \<in> AB; complete AB \<rbrakk> \<Longrightarrow> \<exists>y. Rel r x y \<in> AB \<and> Inst y c \<in> AB" 
  apply (simp add : alc_rule_def list_alc_rules_def completl_cn_some0 )
  done

constdefs
  "clash_free AB ==  \<not> contains_clash AB"

lemma  inverse_exist :
  "\<lbrakk>(i x, i y') \<in> interp_r (can_in i AB) nr ; inj i\<rbrakk> \<Longrightarrow> Rel (AtomR nr) x y' \<in> AB"
  apply ( clarsimp  simp add: can_in_def interp_atom_A_in_AB_dom_def interp_atom_A_in_AB_def rel_ni_atom_role_dom_def rel_ni_atom_role_def inj_on_def )
  apply (subgoal_tac  "x = a")
  apply (subgoal_tac  "y' = b")
  apply clarsimp
  apply auto
  done 

lemma interp_r_inverse_exist:
      " \<lbrakk>inj i; (i x, y) \<in> interp_r (can_in i AB) nr\<rbrakk>  \<Longrightarrow> \<exists>y'. i y' = y"
by (fastsimp  simp add: inj_on_def can_in_def interp_atom_A_in_AB_dom_def interp_atom_A_in_AB_def rel_ni_atom_role_dom_def rel_ni_atom_role_def  )

lemma  can_in_sat_inst: 
 "\<lbrakk> inj i  \<rbrakk> \<Longrightarrow>
  \<forall> AB x.  clash_free AB \<longrightarrow> complete  AB \<longrightarrow> is_Normal_Abox  AB \<longrightarrow> 
  Inst x c \<in> AB  \<longrightarrow> satisfiable_fact (i, (can_in i AB)) (Inst x c)"
  apply (induct c)
    (* Atom   *)
  apply (fast intro: can_in_satis_atom)   
    (* top    *)
  apply (fast intro: can_in_satis_Top)
    (* bot    *)
  apply (simp add: clash_free_def)
  (* negation*)
  apply (fastsimp dest: injD notc_normal_abox
    simp add: clash_free_def can_in_def interp_atom_A_in_AB_dom_def interp_atom_A_in_AB_def)
    (* and *)
  apply (fastsimp simp del: complete.simps dest: completl_cn_and)
    (* or *)
  apply (fastsimp simp del: complete.simps dest: completl_cn_or)
    (* all *) 
  apply (clarsimp simp del: complete.simps) 
  apply (frule completl_cn_all, assumption)
  apply (case_tac role) apply simp
  apply (frule interp_r_inverse_exist ) apply assumption
  apply (fastsimp simp add : inverse_exist )

    (*some*)
  apply (clarsimp simp del: complete.simps) 
  apply (frule completl_cn_some, assumption)
  apply (case_tac role) apply simp
  apply (auto simp add: can_in_def interp_atom_A_in_AB_dom_def interp_atom_A_in_AB_def rel_ni_atom_role_dom_def rel_ni_atom_role_def  )
  done
    (* 

lemma  not_diff_in_succ :
" \<lbrakk> (Diff x y)\<notin>  AB0 ;  ALC_rule  AB0 AB \<rbrakk>  \<Longrightarrow>  (Diff x y) \<notin>  AB"
  by ( fastsimp simp add :  ALC_rule_def ALC_rules_def andrule_simp orruleright_simp orruleleft_simp allrule_simp somerule3_simp)
 *)
lemma can_in_sat_fact:
  "\<lbrakk> inj i  \<rbrakk> \<Longrightarrow>
  \<forall> AB f.  clash_free AB \<longrightarrow> complete  AB \<longrightarrow> is_Normal_Abox  AB \<longrightarrow> 
  f  \<in> AB  \<longrightarrow> satisfiable_fact (i, (can_in i AB)) f"
  apply (clarsimp)
  apply (case_tac f) 
  apply (fastsimp dest:can_in_sat_inst )
  apply (fastsimp dest: can_int_sat_rel)
  done
end

