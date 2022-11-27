lemma moh :
"(list_ex (is_related_all x r c Ab_i ) Ab_i) = (\<exists> y. ((Rel r x y) \<in> set Ab_i \<and> Inst y c \<notin>  set Ab_i ))"
apply auto
apply (induct Ab_i)
apply simp
apply clarsimp
apply (case_tac a)
apply clarsimp
apply (case_tac concept)
apply clarsimp

fun is_related42 ::" 'ni \<Rightarrow> 'nr role \<Rightarrow> ('ni, 'nr, 'nc) fact \<Rightarrow> bool "
  where
  "is_related42 x r f = (\<exists> y. (f = Rel r x y ))"

fun is_related ::" 'ni \<Rightarrow> 'nr role \<Rightarrow> ('ni, 'nr, 'nc) fact \<Rightarrow> bool "
  where
  "is_related x r (Rel r' x' y) = (x = x'  \<and> r = r')"
|   "is_related x r _ = False"

fun is_related_all ::" 'ni \<Rightarrow> 'nr role \<Rightarrow> ('nr, 'nc) concept \<Rightarrow> ('ni, 'nr, 'nc) abox_impl \<Rightarrow> ('ni, 'nr, 'nc) fact \<Rightarrow> bool "
  where
  "is_related_all x r c Ab_i  (Rel r' x' y) = (x = x'  \<and> r = r') \<and> \<not>  (list_ex  (is_x_c_inst y c) Ab_i)"
  "is_related_all x r c Ab_i _ = False "

fun is_related2 ::" 'ni \<Rightarrow> 'nr role \<Rightarrow> ('nr, 'nc) concept \<Rightarrow> ('ni, 'nr, 'nc) abox_impl \<Rightarrow> ('ni, 'nr, 'nc) fact \<Rightarrow> bool "
  where
  "is_related2 x r c Ab_i f = (\<exists> y. (f = Rel r x y ) \<and> \<not>  (list_ex  (is_x_c_inst y c) Ab_i)) "

lemma "is_related x r f = is_related42 x r f"
by (case_tac f) fastsimp+



fun is_related2 ::" 'ni \<Rightarrow> 'nr role \<Rightarrow> ('nr, 'nc) concept \<Rightarrow> ('ni, 'nr, 'nc) abox_impl \<Rightarrow> ('ni, 'nr, 'nc) fact \<Rightarrow> bool "
  where
  "is_related2 x r c Ab_i f = (\<exists> y. (f = Rel r x y ) \<and> \<not>  (list_ex  (is_x_c_inst y c) Ab_i)) "






(*

term "map (my_trans c) (filter (is_related2 x r c Ab_i) Ab_i)"




lemma list_ex_is_x_r_rel0:
  "(list_ex (is_related x r) xs) =( \<exists> y. ( Rel r x y  \<in> set xs))"
  by (induct xs) auto


lemma list_ex_is_related_all :


  "(list_ex (is_related x r) xs) =( \<exists> y. ( Rel r x y  \<in> set xs))"
  by (induct xs) auto

lemma  "list_ex (is_related x r) (filter (is_related2 x r c Ab_i) Ab_i) \<longrightarrow> list_ex (is_related x r) Ab_i "
by (fastsimp simp add: list_ex_is_x_r_rel0 list_ex_is_x_c_inst)



lemma [simp] :" is_related  x r (Rel r x z) "
  by  auto

fun list_of_rel :: " 'ni \<Rightarrow> 'nr role \<Rightarrow> ('ni, 'nr, 'nc) abox_impl \<Rightarrow>('ni, 'nr, 'nc) abox_impl"
  where
  "list_of_rel x r Ab_i =  filter (is_related x r)  Ab_i"

fun list_of_relx :: " 'ni \<Rightarrow> 'nr role \<Rightarrow> ('ni, 'nr, 'nc) abox_impl \<Rightarrow>('ni, 'nr, 'nc) abox_impl"
  where 
  "list_of_relx x r Ab_i = 
  (case Ab_i of [] \<Rightarrow> [] | fact #facts \<Rightarrow> (if (is_related x r fact) then  fact# (list_of_rel x r facts) else  (list_of_rel x r facts) ))"
 
(*
fun list_of_rel :: " 'ni \<Rightarrow> 'nr role \<Rightarrow> ('ni, 'nr, 'nc) abox_impl \<Rightarrow>('ni, 'nr, 'nc) abox_impl"
where 
"list_of_rel x r Ab_i = 
  (case Ab_i of [] \<Rightarrow> [] | fact #facts \<Rightarrow> ( case fact of Rel r x _ \<Rightarrow> fact# (list_of_rel x r facts) | _ \<Rightarrow>(list_of_rel x r facts) ))"


lemma [simp] : " (list_ex (is_x_r_rel x y r) ab_i) \<longrightarrow> (list_ex (is_x_r_rel x y r) (list_of_rel x r ab_i)) "
  apply (clarsimp )
  apply (induct ab_i)
  apply fastsimp+
  done

lemma list_ex_is_x_r_rel2:
  "(list_ex (is_related x r) xs) =( \<exists> y. ( Rel r x y  \<in> set xs))"
  by (induct xs) auto

lemma [simp] : "  (list_ex (is_related x  r) (list_of_rel x r ab_i)) \<longrightarrow> (list_ex (is_related  x  r) ab_i)  "
  apply ( simp add :list_ex_is_x_r_rel2)
  done
lemma [simp] : " (list_ex (is_related  x  r) ab_i) \<longrightarrow> (list_ex (is_related x  r) (list_of_rel x r ab_i))   "
  apply ( simp add :list_ex_is_x_r_rel2)
  done

term foldl

(*
fun list_inst_add_all ::"'ni \<Rightarrow> 'nr role \<Rightarrow> ('nr, 'nc) concept \<Rightarrow>('ni, 'nr, 'nc) abox_impl \<Rightarrow> ('ni, 'nr, 'nc) abox_impl \<Rightarrow>('ni, 'nr, 'nc) abox_impl"
  where
  "list_inst_add_all x r c list_rel ab_i =
        (case  list_rel of 
    [] \<Rightarrow> [] 
    | fact # facts \<Rightarrow> ( if ((is_related x r) fact) then 
         ( if (list_ex (is_x_c_inst y c) ab_i)  then (Inst y c)# (list_inst_add_all x r c facts ab_i) else (list_inst_add_all x r c facts ab_i))
      else (list_inst_add_all x r c facts ab_i)))"

*)

fun list_inst_add_all ::"'ni \<Rightarrow> 'nr role \<Rightarrow> ('nr, 'nc) concept \<Rightarrow>('ni, 'nr, 'nc) abox_impl \<Rightarrow> ('ni, 'nr, 'nc) abox_impl \<Rightarrow>('ni, 'nr, 'nc) abox_impl"
  where
  "list_inst_add_all x r c list_rel ab_i =
        (case  list_rel of 
    [] \<Rightarrow> [] 
    | fact # facts \<Rightarrow>  
          (case fact of 
      Rel r x y \<Rightarrow> ( if (list_ex (is_x_c_inst y c) ab_i)  then (Inst y c)# (list_inst_add_all x r c facts ab_i) else (list_inst_add_all x r c facts ab_i))
      | (Inst _ _ ) \<Rightarrow> (list_inst_add_all x r c facts ab_i)))"

lemma P1 : "list_ex (is_x_c_inst y c ) (list_inst_add_all x r c (list_of_rel x r ab_i) ab_i) \<Longrightarrow>  list_ex (is_x_r_rel x y r ) ab_i "
apply clarsimp
apply (case_tac  ab_i)
apply clarsimp
apply clarsimp
apply (case_tac a)
apply  auto
apply (case_tac list)
apply clarsimp 
apply (fastsimp)
done

*)*)
term "filter (is_related_all_test x r c Ab_i)"

fun action_all :: "('ni, 'nr, 'nc) action"
where
  "action_all (prefix, (Inst x (AllC r c)) , suffix) = 
  ( map (my_trans c )( filter (is_related_all_test x r c (prefix @ [Inst x (AllC r c)] @ suffix)) (prefix @ [Inst x (AllC r c)] @ suffix))) 

@ prefix @ [Inst x (AllC r c)] @ suffix"
  | "action_all  _  = []"





constdefs all_rule ::"('ni, 'nr, 'nc) srule" 
  "all_rule == Rule (appcond_all, action_all)"



(***********************************************)
(***********************************************)
(***********************************************)
(*************      some rule     **************)
(***********************************************)
(***********************************************)








(*** (to do) do the same for others rules *)


fun apply_rule :: 
  "('ni, 'nr, 'nc) srule \<Rightarrow>('ni, 'nr, 'nc) abox_impl \<Rightarrow> ('ni, 'nr, 'nc) tableau " 
  where 
  "apply_rule (Rule(appc, act)) ab_i =
  map act (split_appcond appc [] ab_i ab_i)"

(*** here indeterministe with tow action, this used for or_rule 
best if we define list of action for rule*)

fun apply_rule_ind :: 
  "(('ni, 'nr, 'nc) srule * ('ni, 'nr, 'nc) srule) \<Rightarrow>('ni, 'nr, 'nc) abox_impl \<Rightarrow> ('ni, 'nr, 'nc) tableau " 
  where 
  "apply_rule_ind ((Rule(appc, act)), (Rule(appc1, act1))) ab_i = 
  (map act (split_appcond appc [] ab_i ab_i)) @ (map act1 (split_appcond appc1 [] ab_i ab_i)) "


term "apply_rule and_rule"
term "apply_rule_ind (or_rule_left, or_rule_right)"

lemma   correct_implementation_and :
  "sound_rule_impl set Andrule (apply_rule and_rule) "
  apply (clarsimp simp add : sound_rule_impl_def)
  apply (clarsimp simp add: and_rule_def)
  apply (frule split_appcond_invariant3)
  apply simp
  apply (clarsimp simp add: appcond_and_rewr)
  apply (rule mk_andrule) apply fastsimp
  apply (fastsimp simp add: list_ex_is_x_c_inst)+
  done

lemma   correct_implementation_or_left :
  "sound_rule_impl set Orruleleft  (apply_rule or_rule_left) "
  apply (clarsimp simp add : sound_rule_impl_def)
  apply (clarsimp simp add: or_rule_left_def)
  apply (frule split_appcond_invariant3)
  apply simp
  apply (clarsimp simp add: appcond_or_rewr)
  apply (rule mk_orruleleft) apply fastsimp
  apply (fastsimp simp add: list_ex_is_x_c_inst)+
  done

lemma   correct_implementation_or_right :
  "sound_rule_impl set Orruleright  (apply_rule or_rule_right) "
  apply (clarsimp simp add : sound_rule_impl_def)
  apply (clarsimp simp add: or_rule_right_def)
  apply (frule split_appcond_invariant3)
  apply simp
  apply (clarsimp simp add: appcond_or_rewr)
  apply (rule mk_orruleright) apply fastsimp
  apply (fastsimp simp add: list_ex_is_x_c_inst)+
  done

definition Orrule:: " (('ni,'nr,'nc) rule)"
  where 
  "Orrule a b == (Orruleleft a b) \<or> (Orruleright a b)"

lemma   correct_implementation_or :
  "sound_rule_impl set Orrule (apply_rule_ind (or_rule_left,or_rule_right)) "
  apply (clarsimp simp add : sound_rule_impl_def Orrule_def)
  apply (clarsimp simp add: or_rule_right_def or_rule_left_def )
  apply auto
  apply (frule split_appcond_invariant3)
  apply simp
  apply (clarsimp simp add: appcond_or_rewr)
  apply (fastsimp simp add : orruleleft_simp orruleright_simp list_ex_is_x_c_inst)
  apply (frule split_appcond_invariant3)
  apply simp
  apply (clarsimp simp add: appcond_or_rewr)
  apply (clarsimp simp add : orruleleft_simp orruleright_simp)apply (fastsimp simp add: list_ex_is_x_c_inst)+
  done



(*
lemma   complete_implementation_and :
  "complete_rule_impl_set set Andrule (apply_rule and_rule) "
  apply (clarsimp simp add : complete_rule_impl_set_def)
  apply (clarsimp simp add: and_rule_def )
 apply(case_tac ai)
 apply (simp add: andrule_simp)
 apply (case_tac a)
 defer
 apply simp
 apply (clarsimp simp add: appcond_and_rewr andrule_simp)  
apply auto
  apply (simp add: split_appcond_invariant)
apply auto
 apply (clarsimp simp add: andrule_simp)
apply (clarsimp simp add: list_ex_is_x_c_inst)
  apply (rule split_appcond_invariant3)
  apply (frule split_appcond_invariant3)
  apply simp
  apply (clarsimp simp add: appcond_and_rewr)
  apply (rule mk_andrule) apply fastsimp
  apply (fastsimp simp add: list_ex_is_x_c_inst)
  apply blast
  done

*)
(* mybe this function not good cant extracted 

fun appcond_all0 :: "('ni, 'nr, 'nc) appcond"
  where
    "appcond_all0 Ab_i (Inst x (AllC r c)) = 
     (\<exists>  y.  (( (list_ex (is_x_r_rel  x y r) Ab_i )) \<and> \<not> (list_ex (is_x_c_inst y c) Ab_i )))"
    |"appcond_all0 Ab_i  _  = False"

export_code appcond_all in OCaml file "appcond_all.ml "*)



(*
fun apply_rule_ind :: 
  "(('ni, 'nr, 'nc) srule * ('ni, 'nr, 'nc) srule) \<Rightarrow>('ni, 'nr, 'nc) abox_impl \<Rightarrow> ('ni, 'nr, 'nc) tableau " 
  where 
  "apply_rule_ind ((Rule(appc, act)), (Rule(appc1, act1))) ab_i = 
  (map act (split_appcond appc [] ab_i ab_i)) @ (map act1 (split_appcond appc1 [] ab_i ab_i)) "


term "apply_rule and_rule"
term "apply_rule_ind (or_rule_left, or_rule_right)"
*)
(*
definition Orrule:: " (('ni,'nr,'nc) rule)"
  where 
  "Orrule a b == (Orruleleft a b) \<or> (Orruleright a b)"

lemma   correct_implementation_or :
  "sound_rule_impl set Orrule (apply_rule_ind (or_rule_left,or_rule_right)) "
  apply (clarsimp simp add : sound_rule_impl_def Orrule_def)
  apply (clarsimp simp add: or_rule_right_def or_rule_left_def )
  apply auto
  apply (frule split_appcond_invariant3)
  apply simp
  apply (clarsimp simp add: appcond_or_rewr)
  apply (fastsimp simp add : orruleleft_simp orruleright_simp list_ex_is_x_c_inst)
  apply (frule split_appcond_invariant3)
  apply simp
  apply (clarsimp simp add: appcond_or_rewr)
  apply (clarsimp simp add : orruleleft_simp orruleright_simp)apply (fastsimp simp add: list_ex_is_x_c_inst)+
  done
*)
(*
lemma "y \<in> f c ` {x \<in> set a. P a c} = X"
apply (simp add: image_def)
*)