theory Tableau imports Semantic

begin
(********** Abox    ****************************)

text {* Abox is set (finite) of assertional axiom  where axiom is defined *}

datatype  ('ni,'nr,'nc) fact  = 
  Inst   "'ni" "('nr,'nc)concept"
  | Rel  "'nr role" "'ni " "'ni"
 (* | Diff "'ni" "'ni"*)

fun  is_fact_normal ::"('ni,'nr,'nc) fact \<Rightarrow> bool" 
  where
    "is_fact_normal (Inst x c) = isNF c"
  | "is_fact_normal (Rel r x y) = True"
  (*| "is_fact_normal (Diff x y) = True"*)

fun fact_normal :: "('ni,'nr,'nc) fact \<Rightarrow>('ni,'nr,'nc) fact"
where 
  "fact_normal (Inst x c) = Inst x (NNF c)"
  |"fact_normal (Rel r x y) = Rel r x y"
  (*|"fact_normal (Diff x y) = Diff x y"*)

types
 ('ni,'nr,'nc) abox = "(('ni,'nr,'nc) fact) set"


(**************** some exampls**************** Evaluation *)
normal_form  " NNF (NotC (AndC Top (NotC (NotC (AtomC 0)))))"
normal_form  " fact_normal (Inst 0 (NotC (AndC Top (NotC (NotC (AtomC 0))))))"
term "{Diff 0 0, Rel (AtomR 0) 1 2}"
term "{Rel (AtomR 0) 1 2} ::  (nat,nat, nat) abox "

(************** end of exampls*************************)

definition  is_Normal_Abox :: "(('ni,'nr,'nc) abox) \<Rightarrow> bool"
   where
     "is_Normal_Abox Ab =  (\<forall>f. f\<in> Ab \<longrightarrow> (is_fact_normal f))"

fun satisfiable_fact :: " (('ni Interp_inst) * (('nr, 'nc) Interp) ) \<Rightarrow> ('ni,'nr,'nc) fact \<Rightarrow> bool"
   where
 " satisfiable_fact (ii, icr) (Inst x c)  = ((ii x) \<in> (interpC icr c)) "
| " satisfiable_fact (ii, icr) (Rel r x y)  = ((ii x, ii y) \<in> (interpR icr r)) "
(*| " satisfiable_fact (ii, icr) (Diff x y)  = ((ii x) \<noteq> (ii y)) "*)

definition satisfiable_abox :: "(('ni,'nr,'nc) abox) \<Rightarrow> bool"
   where
     " satisfiable_abox Ab =  (\<exists> i. (\<forall> f\<in> Ab. satisfiable_fact i f))"

lemma  sat_Top_abox : 
  " satisfiable_abox { Inst x Top}"
  by (simp add: satisfiable_abox_def)

lemma not_sat_bottom_abox :
  "\<not>  satisfiable_abox { Inst x Bottom}"
  by (simp add: satisfiable_abox_def)

    (************* Semantics Tableau *****************)
text{* formalisation of complation rules
  we start with classical coding, useing inductive predicat on  one branch *}
  (**********************************************)

text{* and rule  *}

types
 ('ni,'nr,'nc) rule = "(('ni,'nr,'nc) abox) \<Rightarrow> (('ni,'nr,'nc) abox) \<Rightarrow> bool"  


constdefs 
  and_applicable :: "(('ni,'nr,'nc) abox) \<Rightarrow> ('ni,'nr,'nc) fact \<Rightarrow> bool" 
 "and_applicable AB f \<equiv>
  (\<exists> x c1 c2. (f = (Inst x (AndC c1 c2)) \<and>
   f \<in>AB  \<and>  \<not> ((Inst x c1)\<in>AB  \<and> (Inst x c2)\<in>AB)))"


  (* TODO: 
  * name rules differently (preferably with lower-case letters: andrule
  * convert rules into definitions and delete the inductive rules.
  Thus, andrule_simp becomes the definition of andrule
  *)

inductive  Andrule  :: "('ni,'nr,'nc) rule"
  where
  mk_andrule: 
  "\<lbrakk> and_applicable b1 (Inst x (AndC c1 c2));
  b2 = {Inst x c2, Inst x c1} \<union> b1 \<rbrakk>
  \<Longrightarrow> Andrule b1 b2" 

lemma andrule_simp :
  "(Andrule  b1 b2) = 
  (\<exists> x c1 c2. and_applicable b1 (Inst x (AndC c1 c2)) \<and>
   b2 = {Inst x c2, Inst x c1} \<union> b1)"
  apply (rule iffI)
  apply (induct rule: Andrule.induct)
  apply fastsimp
  apply (fast intro: mk_andrule)
  done


text{* or rule *}
 
(* or Left*)

inductive  Orruleleft :: "('ni,'nr,'nc) rule"
  where
  mk_orruleleft  : 
  "\<lbrakk> Inst x (OrC c1 c2) \<in> b1; 
  \<not> (Inst x c1) \<in> b1  ; \<not>  (Inst x c2 ) \<in> b1;
  b2 =  {Inst x c1} \<union>  b1 \<rbrakk>
  \<Longrightarrow> Orruleleft b1 b2" 

(* or right *)

inductive  Orruleright:: "('ni,'nr,'nc) rule"
where
  mk_orruleright  : 
  "\<lbrakk> Inst x (OrC c1 c2) \<in> b1; 
  \<not> (Inst x c1) \<in> b1  ; \<not>  (Inst x c2 ) \<in> b1;
  b2 = insert (Inst x c2)  b1 \<rbrakk>
  \<Longrightarrow> Orruleright b1 b2" 


inductive  Orrule:: "('ni,'nr,'nc) rule"
where
  mk_orrule : 
  "\<lbrakk> Inst x (OrC c1 c2) \<in> b1; 
  \<not> (Inst x c1) \<in> b1  ; \<not>  (Inst x c2 ) \<in> b1;
  b2 = insert (Inst x c1)  b1 \<or> b2 = insert (Inst x c2)  b1 \<rbrakk>
  \<Longrightarrow> Orrule b1 b2" 


text{* allrule *}

inductive Allrule :: "('ni,'nr,'nc) rule"
where  
  mk_Allrule :
  "\<lbrakk> Inst x (AllC r c1) \<in> b1; 
  (Rel r x y ) \<in> b1  ; \<not>  (Inst y c1 ) \<in> b1;
  b2 =  insert (Inst y c1)  b1 \<rbrakk>
  \<Longrightarrow>  Allrule b1 b2"

text{* some rule *}

fun  occurs_ni_in_fact ::  " 'ni \<Rightarrow> ('ni,'nr,'nc) fact \<Rightarrow> bool"  
  where   
  " occurs_ni_in_fact x (Inst z  c)        =  (x = z) "
  | " occurs_ni_in_fact x (Rel r ni1 ni2)  =  (x = ni1 \<or> x =ni2) "
(*  | " occurs_ni_in_fact x (Diff ni1 ni2)   =  (x = ni1 \<or> x =ni2) "*)

fun occurs_ni_in_abox :: " 'ni \<Rightarrow> ('ni,'nr,'nc) abox \<Rightarrow> bool"   
  where 
  "occurs_ni_in_abox x ab = (\<exists> f \<in> ab. (occurs_ni_in_fact x f)) "
 
fun not_occurs_ni_in_abox :: " 'ni \<Rightarrow> ('ni,'nr,'nc) abox \<Rightarrow> bool"   
  where 
  "not_occurs_ni_in_abox  x ab = (\<forall>f \<in> ab. \<not> (occurs_ni_in_fact x f)) "

lemma not_occurs_in :
  " (not_occurs_ni_in_abox x ab) =  (\<not>  (occurs_ni_in_abox  x ab))"
  apply (rule iffI)apply fastsimp
  apply simp
  done

fun set_ni_in_abox1 :: " ('ni,'nr,'nc) abox \<Rightarrow> 'ni set "
where 
" set_ni_in_abox1 AB ={ x. occurs_ni_in_abox x AB} "

fun set_ni_notin_abox ::" ('ni,'nr,'nc) abox \<Rightarrow> 'ni set "
 where 
" set_ni_notin_abox AB = - set_ni_in_abox1 AB "

lemma not_in_set_ni :
  " \<lbrakk> not_occurs_ni_in_abox x AB \<rbrakk> \<Longrightarrow> x \<in> - (set_ni_in_abox1 AB) "
  by simp 

inductive Somerule :: "('ni,'nr,'nc) rule"
  where 
  mk_Somerule :
  "\<lbrakk>(Inst x (SomeC r c1 )) \<in> b1 ;
   \<forall> y. ~ ((Rel r x y ) \<in> b1 \<and> (Inst y c1) \<in> b1);
   (not_occurs_ni_in_abox z b1);
   b2 = insert (Rel r x z) (insert (Inst z c1) b1)
  \<rbrakk> 
  \<Longrightarrow> Somerule b1 b2"

inductive Somerule_gen :: 
  "((('ni,'nr,'nc) abox) \<Rightarrow> 'ni) \<Rightarrow> ('ni,'nr,'nc) rule"
  where 
  mk_Somerule_gen :
  "\<lbrakk>(Inst x (SomeC r c1 )) \<in> b1 ;
   \<forall> y. ~ ((Rel r x y ) \<in> b1 \<and> (Inst y c1) \<in> b1);
   z = gen b1;
   b2 = insert (Rel r x z) (insert (Inst z c1) b1)
  \<rbrakk> 
  \<Longrightarrow> Somerule_gen gen b1 b2"


inductive Somerule2 :: " (('ni,'nr,'nc) abox) \<Rightarrow> (('ni,'nr,'nc) abox) \<Rightarrow> bool"
  where 
  mk_Somerule2 :
  "\<lbrakk>(Inst x (SomeC r c1 )) \<in> b1 ;
   \<forall> y. ~ ((Rel r x y ) \<in> b1 \<and> (Inst y c1) \<in> b1);
   z \<in> set_ni_notin_abox b1;
   b2 = insert (Rel r x z) (insert (Inst z c1) b1)
  \<rbrakk> 
  \<Longrightarrow> Somerule2 b1 b2"

inductive Somerule3 :: " (('ni,'nr,'nc) abox) \<Rightarrow> (('ni,'nr,'nc) abox) \<Rightarrow> bool"
  where 
  mk_Somerule3 :
  "\<lbrakk>(Inst x (SomeC r c1 )) \<in> b1 ;
   \<forall> y. ~ ((Rel r x y ) \<in> b1 \<and> (Inst y c1) \<in> b1);
   b2 = insert (Rel r x (SOME b.(not_occurs_ni_in_abox b b1) )) (insert (Inst (SOME b.(not_occurs_ni_in_abox b b1)) c1) b1)  \<rbrakk> 
  \<Longrightarrow> Somerule3 b1 b2"



(******** rule as disjunction of these rules *)

definition list_alc_rules :: " (('ni,'nr,'nc) rule) list"
  where
  "list_alc_rules =
  [ Andrule , Orruleleft ,  Orruleright ,  Allrule , Somerule3]"


fun empty_rule :: "('ni,'nr,'nc) rule"
where "empty_rule a b = False"

fun  disj_rule  ::
  "('ni,'nr,'nc) rule \<Rightarrow> ('ni,'nr,'nc) rule \<Rightarrow> ('ni,'nr,'nc) rule" 
  where "disj_rule r1 r2 = (\<lambda>  a b.  r1 a b  \<or>  r2 a b)"

fun  disj_rule_list  :: "('ni,'nr,'nc) rule list  \<Rightarrow> ('ni,'nr,'nc) rule" 
  where 
  " disj_rule_list [] = empty_rule "
  |" disj_rule_list (r#rs) =  disj_rule r (disj_rule_list rs)"

definition  alc_rule :: "('ni,'nr,'nc) rule"
  where 
  "alc_rule = disj_rule_list list_alc_rules"

(*****************Simplifications **********************************)


lemma orruleleft_simp :
  "(Orruleleft  b1 b2) =   (\<exists> x c1 c2. (Inst x (OrC c1 c2) \<in> b1 \<and>  
  \<not> ((Inst x c1) \<in> b1)  \<and> \<not>  ((Inst x c2 ) \<in> b1)) \<and> b2 = ( insert (Inst x c1)   b1))  "
  apply (rule iffI)
  apply (induct rule: Orruleleft.induct)
  apply fastsimp
  apply (fast intro: mk_orruleleft) 
  done

lemma orruleright_simp :
  "(Orruleright  b1 b2) =   (\<exists> x c1 c2. (Inst x (OrC c1 c2) \<in> b1 \<and>  
  \<not> ((Inst x c1) \<in> b1)  \<and> \<not>  ((Inst x c2 ) \<in> b1)) \<and> b2 = ( insert (Inst x c2)  b1))  "
  apply (rule iffI)
  apply (induct rule: Orruleright.induct)
  apply fastsimp
  apply (fast intro: mk_orruleright) 
  done


lemma orrule_simp :
  "(Orrule b1 b2) =   
  (\<exists> x c1 c2. (Inst x (OrC c1 c2) \<in> b1 \<and>  
  \<not> ((Inst x c1) \<in> b1)  \<and> \<not>  ((Inst x c2 ) \<in> b1)) \<and> 
  ((b2 = insert (Inst x c1) b1) \<or> (b2 = insert (Inst x c2) b1)))"
  apply (rule iffI)
  apply (induct rule: Orrule.induct)
  apply fastsimp
  apply (fast intro: mk_orrule) 
  done


lemma orrule_disj:
  "Orrule a b = (Orruleleft a b \<or> Orruleright a b)"
by (simp add: orrule_simp orruleleft_simp orruleright_simp) blast


lemma allrule_simp :
  "(Allrule  b1 b2) = 
  (\<exists> x y r c1 . Inst x (AllC r c1) \<in> b1 \<and> 
  (Rel r x y ) \<in> b1  \<and>   (Inst y c1 ) \<notin>  b1 \<and>
  b2 = insert (Inst y c1) b1 )"
  apply (rule iffI)
  apply (induct rule: Allrule.induct)
  apply fastsimp
  apply (fast intro: mk_Allrule) 
  done

lemma somerule_simp :
" Somerule b1 b2 = (\<exists> x z c1 r.  (Inst x (SomeC r c1 )) \<in> b1 \<and> (\<forall> y.
                      ~ ((Rel r x y ) \<in> b1 \<and>  (Inst y c1 ) \<in> b1) ) \<and>
                        (not_occurs_ni_in_abox z b1) \<and>
                        b2 = insert (Rel r x z )  ( insert (Inst z c1) b1 ) )"
  apply (rule iffI)
  apply (induct rule: Somerule.induct)
  apply fast
  apply (fast intro: mk_Somerule)
  done

lemma somerule_gen_simp :
  "Somerule_gen gen b1 b2 = (\<exists> x z c1 r.  (Inst x (SomeC r c1 )) \<in> b1 \<and> (\<forall> y.
                      ~ ((Rel r x y ) \<in> b1 \<and>  (Inst y c1 ) \<in> b1) ) \<and>
                        z = gen b1 \<and>
                        b2 = insert (Rel r x z )  ( insert (Inst z c1) b1 ) )"
  apply (rule iffI)
  apply (induct rule: Somerule_gen.induct)
  apply fast
  apply (fast intro: mk_Somerule_gen)
  done


lemma somerule2_simp :
" Somerule2 b1 b2 = (\<exists> x z c1 r.  (Inst x (SomeC r c1 )) \<in> b1 \<and> (\<forall> y.
                      ~ ((Rel r x y ) \<in> b1 \<and>  (Inst y c1 ) \<in> b1) ) \<and>
                       z \<in> set_ni_notin_abox b1 \<and>
                        b2 = insert (Rel r x z )  ( insert (Inst z c1) b1 ) )"
  apply (rule iffI)
  apply (induct rule: Somerule2.induct)
  apply fast
  apply (fast intro: mk_Somerule2) 
  done

lemma somerule3_simp :

" Somerule3 b1 b2 = (\<exists> x c1 r .  (Inst x (SomeC r c1 )) \<in> b1 \<and> (\<forall> y.
                      ~ ((Rel r x y ) \<in> b1 \<and>  (Inst y c1 ) \<in> b1) ) \<and>
                       (\<lambda> z. b2 = insert (Rel r x z) (insert (Inst z c1) b1)) (SOME b.(not_occurs_ni_in_abox b b1) )) "
  apply (rule iffI)
  apply (induct rule: Somerule3.induct)
  apply fast
  apply (fast intro: mk_Somerule3) 
  done
(*** end smplification **)

lemma   andrule_preserve_nnf0 : 
  "   Andrule  AB1 AB2 \<longrightarrow>  is_Normal_Abox AB1 \<longrightarrow>is_Normal_Abox AB2 "
  by (fastsimp simp add: andrule_simp and_applicable_def is_Normal_Abox_def)

(**********************)
lemma andrule_preserve_nnf :
  " \<lbrakk> Andrule  AB1 AB2;  is_Normal_Abox AB1  \<rbrakk> \<Longrightarrow> is_Normal_Abox AB2 "
  by (fastsimp simp add: andrule_simp and_applicable_def is_Normal_Abox_def)

lemma orruleleft_preserve_nnf :
  " \<lbrakk> Orruleleft  AB1 AB2;  is_Normal_Abox AB1  \<rbrakk> \<Longrightarrow> is_Normal_Abox AB2 "
  by (fastsimp simp add: orruleleft_simp is_Normal_Abox_def)

lemma orruleright_preserve_nnf :
  " \<lbrakk> Orruleright AB1 AB2;  is_Normal_Abox AB1  \<rbrakk> \<Longrightarrow> is_Normal_Abox AB2 "
  by (fastsimp simp add: orruleright_simp is_Normal_Abox_def)

lemma orrule_preserve_nnf :
  " \<lbrakk> Orrule AB1 AB2;  is_Normal_Abox AB1  \<rbrakk> \<Longrightarrow> is_Normal_Abox AB2 "
  by (fastsimp simp add: orrule_simp is_Normal_Abox_def)

lemma allrule_preserve_nnf :
  " \<lbrakk> Allrule  AB1 AB2;  is_Normal_Abox AB1  \<rbrakk> \<Longrightarrow> is_Normal_Abox AB2 "
  apply( simp add: is_Normal_Abox_def)
  apply (induct rule: Allrule.induct)
  apply fastsimp
  done

lemma somerule_preserve_nnf :
  " \<lbrakk> Somerule  AB1 AB2;  is_Normal_Abox AB1  \<rbrakk> \<Longrightarrow> is_Normal_Abox AB2 "
  by (fastsimp simp add: somerule_simp is_Normal_Abox_def)

lemma somerule3_preserve_nnf :
  " \<lbrakk> Somerule3  AB1 AB2;  is_Normal_Abox AB1  \<rbrakk> \<Longrightarrow> is_Normal_Abox AB2 "
  by (fastsimp simp add: somerule3_simp is_Normal_Abox_def)

lemma andrule_add :
  "Andrule  b1 b2 \<Longrightarrow>  (\<exists> x c1 c2. b2 = insert (Inst x c2) (insert (Inst x c1) b1))  "
  apply (induct rule: Andrule.induct)
  apply fastsimp  
  done

lemma alc_rule_preserve_nnf :
  " \<lbrakk> alc_rule  AB1 AB2;  is_Normal_Abox AB1  \<rbrakk> \<Longrightarrow> is_Normal_Abox AB2 "
by (auto simp add: alc_rule_def list_alc_rules_def
  andrule_preserve_nnf  orruleleft_preserve_nnf orruleright_preserve_nnf somerule3_preserve_nnf allrule_preserve_nnf)
end


