theory Implementation  imports Tableau Completeness
begin

types
 ('ni,'nr,'nc) abox_impl = "(('ni,'nr,'nc) fact) list"

 types
 ('ni,'nr,'nc) rule_impl = "(('ni,'nr,'nc) abox_impl) \<Rightarrow> ('ni,'nr,'nc) abox_impl list"

types ('ni, 'nr, 'nc) tableau  =" ('ni, 'nr, 'nc) abox_impl list"


(* Rules  *)

types ('ni, 'nr, 'nc) appcond   = "('ni, 'nr, 'nc) abox_impl \<Rightarrow> ('ni, 'nr, 'nc) fact \<Rightarrow> ('ni, 'nr, 'nc) fact option "

types ('ni, 'nr, 'nc) action = "('ni, 'nr, 'nc) abox_impl \<Rightarrow> ('ni, 'nr, 'nc) fact \<Rightarrow>  ('ni, 'nr, 'nc) tableau"


datatype ('ni, 'nr, 'nc) srule  = 
  Rule " ('ni, 'nr, 'nc) appcond * ('ni, 'nr, 'nc) action"

(** some properties **)
constdefs 
   correct_implementation :: "(('ni,'nr,'nc) abox_impl \<Rightarrow> ('ni,'nr,'nc) abox) \<Rightarrow> (('ni,'nr,'nc) rule) \<Rightarrow> (('ni,'nr,'nc) rule_impl) \<Rightarrow> bool"
   "correct_implementation abstr r r_impl ==  \<forall>  ai ai'. (r (abstr ai) (abstr ai')) \<longrightarrow>  ai' \<in> set (r_impl ai) "

 constdefs 
   complete_implementation :: "(('ni,'nr,'nc) abox_impl \<Rightarrow> ('ni,'nr,'nc) abox) \<Rightarrow> (('ni,'nr,'nc) rule) \<Rightarrow> (('ni,'nr,'nc) rule_impl) \<Rightarrow> bool"
   "complete_implementation abstr r r_impl ==  \<forall>  ai ai'.  ai' \<in> set (r_impl ai) \<longrightarrow> (r (abstr ai) (abstr ai'))"

(*** Rules implementation ***)

fun  lift_appcond  ::" (('ni, 'nr, 'nc) appcond) 
                       \<Rightarrow> ('ni, 'nr, 'nc) abox_impl
                         \<Rightarrow>('ni, 'nr, 'nc) abox_impl
                            \<Rightarrow> (('ni, 'nr, 'nc) fact option )" 
  where
  "lift_appcond appc Ab_i  [] =  None"
  | "lift_appcond appc  Ab_i (fct # fcts) = 
     ( case (appc Ab_i  fct) of  
                    None  \<Rightarrow> lift_appcond appc Ab_i fcts  
                  | Some fct1  \<Rightarrow> Some fct1) "

fun is_x_c_inst :: "'ni \<Rightarrow> ('nr, 'nc) concept \<Rightarrow> ('ni, 'nr, 'nc) fact\<Rightarrow> bool"
  where 
  "is_x_c_inst x c f =  (f = Inst x c)"

(**** And rule ***)
fun appcond_and :: "('ni, 'nr, 'nc) abox_impl \<Rightarrow> ('ni, 'nr, 'nc) fact  \<Rightarrow> ('ni, 'nr, 'nc) fact option" 
  where
    "appcond_and Ab_i (Inst x (AndC c1 c2)) = 
         (if (list_ex (is_x_c_inst x c1) Ab_i ) \<and> (list_ex (is_x_c_inst x c2) Ab_i ) 
          then None else  Some (Inst x (AndC c1 c2))) "
    |"appcond_and Ab_i  _  = None"



fun  action_and :: "('ni, 'nr, 'nc) abox_impl \<Rightarrow> ('ni, 'nr, 'nc) fact \<Rightarrow> ('ni, 'nr, 'nc) tableau "
  where
  "action_and  Ab_i (Inst x (AndC c1 c2)) =  [(Inst x c1)#((Inst x c2)#Ab_i)]"
  | "action_and  Ab_i  _  = []"


constdefs and_rule ::"('ni, 'nr, 'nc) srule"  "and_rule == Rule (appcond_and, action_and)"

(*** (to do) do the same for others rules *)

fun apply_rule :: "('ni, 'nr, 'nc) srule \<Rightarrow>('ni, 'nr, 'nc) abox_impl \<Rightarrow> ('ni, 'nr, 'nc) tableau " 
  where 
  " apply_rule  (Rule(appc, act)) Ab_i =
  (case ( lift_appcond appc Ab_i Ab_i) of
  None \<Rightarrow> [Ab_i]
  | Some fct \<Rightarrow> act Ab_i fct )"

term "apply_rule and_rule"

(*** (apply_rule and_rule) ::  rule_impl ***)


(* contains_clash_impl  *)

fun is_neg_inst :: "('ni,'nr,'nc) fact \<Rightarrow> ('ni,'nr,'nc) fact \<Rightarrow> bool"
where
  "is_neg_inst (Inst x c) f = (f = (Inst x (NotC c)))"
| "is_neg_inst _ f = False"

lemma [simp]: "is_neg_inst (Inst x c)  (Inst x (NotC c))"
  by simp

fun is_bot_inst :: "('ni,'nr,'nc) fact \<Rightarrow> bool"
where
  "is_bot_inst (Inst x Bottom) = True"
| "is_bot_inst _  = False"


fun contains_clash_impl :: "('ni,'nr,'nc) abox_impl \<Rightarrow> bool  "
  where
  " contains_clash_impl AB = ((list_ex  (\<lambda> x. (list_ex (is_neg_inst x) AB)) AB) \<or> (list_ex is_bot_inst AB))"


(**** those proofs are not optimized **)

lemma [simp] :
  "(list_ex  (\<lambda> x. (list_ex (is_neg_inst x) AB)) AB) \<Longrightarrow> (\<exists> x c. ((Inst x c) \<in> (set AB) \<and> (Inst x (NotC c)) \<in>( set AB)) ) "
  apply (clarsimp  simp add: list_ex_iff)
  apply (case_tac x)
  apply fastsimp+
  done

lemma [simp] :
  "(\<exists> x c. ((Inst x c) \<in> (set AB) \<and> (Inst x (NotC c)) \<in>( set AB)) )\<Longrightarrow> (list_ex  (\<lambda> x. (list_ex (is_neg_inst x) AB)) AB)"
  apply (clarsimp  simp add: list_ex_iff)
  apply (subgoal_tac "is_neg_inst (Inst x c) (Inst x (NotC c))")
  apply blast
  apply simp
  done

lemma [simp] :
  "(\<exists> x c. ((Inst x c) \<in> (set AB) \<and> (Inst x (NotC c)) \<in>( set AB)) ) = (list_ex  (\<lambda> x. (list_ex (is_neg_inst x) AB)) AB)"
  apply (rule iffI)
  apply simp+
  done

lemma [simp]: "list_ex is_bot_inst AB = (\<exists>x. Inst x Bottom \<in> set AB)"
  apply (induct AB)
  apply simp
  apply simp
  apply (case_tac a)
  apply simp
  apply (case_tac concept)
  apply fastsimp+
  done

(*** good proof*)
lemma contains_clash_impl_contains_clash: "contains_clash_impl ab_i = contains_clash (set ab_i)"
  apply (rule iffI)
  apply simp
  apply (clarsimp  simp add: list_ex_iff)
  apply auto
  defer
  apply (clarsimp  simp add: list_ex_iff)
  apply (subgoal_tac "is_neg_inst (Inst x c) (Inst x (NotC c))")
  apply blast
  apply simp
  apply (case_tac x)
  apply fastsimp+
  done

    (***false*)

    (* lemma complete_implementation_and : "complete_implementation set Andrule
    (apply_rule and_rule) " apply (clarsimp simp add :
    complete_implementation_def (* andrule_simp and_rule_def option_case_def*) )
    apply (clarsimp simp add : andrule_simp ) apply (case_tac ai ) apply (clarsimp
    simp add: and_rule_def)

    *)


    (*** for testing *)

constdefs "AB_list==[(Inst (0::nat) (AndC (AtomC (1::nat)) (AtomC (2::nat)))) , (Inst (4::nat) (AndC (AtomC (1::nat)) (AtomC (2::nat))))]"
normal_form " (apply_rule and_rule) [(Inst (0::nat) (AndC (AtomC (1::nat)) (AtomC 2))), (Inst (4::nat) (AndC (AtomC (1::nat)) (AtomC (2::nat))))]" 
normal_form "(apply_rule and_rule)[Inst 0 (AtomC (Suc 0)), Inst 0 (AtomC (Suc (Suc 0))), Inst 0 (AndC (AtomC (Suc 0)) (AtomC (Suc (Suc 0)))),
  Inst (Suc (Suc (Suc (Suc 0)))) (AndC (AtomC (Suc 0)) (AtomC (Suc (Suc 0))))]"
 (*
lemma tttt:
  "\<exists> ai'. (Andrule (set AB_list) (set ai') \<longrightarrow> set ai' \<in> (set` (set (apply_rule and_rule AB_list))))"
  apply (clarsimp simp add :   andrule_simp and_rule_def AB_list_def)

  apply
  apply clarsimp
  apply auto
done
*)
lemma   correct_implementation_and :
  "correct_implementation set  Andrule (apply_rule and_rule) "
  apply (clarsimp simp add : correct_implementation_def) (*  andrule_simp and_rule_def*)
  apply (case_tac ai )
  apply (clarsimp simp add :  andrule_simp and_rule_def ) 
  apply (clarsimp simp add :  andrule_simp and_rule_def )
  apply ( case_tac a) defer
  apply clarsimp
  apply clarsimp
 




end
correct_implementation :: "(('ni,'nr,'nc) abox_impl \<Rightarrow> ('ni,'nr,'nc) abox) \<Rightarrow> (('ni,'nr,'nc) rule) \<Rightarrow> (('ni,'nr,'nc) rule_impl) \<Rightarrow> bool"
   "correct_implementation abstr r r_impl ==  \<forall>  ai ai'. (r (abstr ai) (abstr ai')) \<longrightarrow>  ai' \<in> set (r_impl ai) "

end
 









(* faux 
constdefs 
"correct_implementation abstr r r_impl ==  \<forall>  a a'. (r a a') \<longrightarrow>  (abstr a') \<in> set (r_impl (abstr a)) "
  a  reconsiderer
constdefs 
"complete_implementation abstr r r_impl ==  \<forall>  a a'. (r_impl (abstr a) (abstr a')) \<longrightarrow> (r a a')"
*)
