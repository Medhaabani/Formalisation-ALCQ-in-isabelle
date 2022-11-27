theory Soundness imports Tableau
begin
(*************************soundness *****************************)

constdefs
  sound :: "('ni,'nr,'nc) rule \<Rightarrow> bool"
  "sound r == \<forall> A1 A2. r A1 A2 \<longrightarrow> satisfiable_abox A2 \<longrightarrow> satisfiable_abox A1"

  (* Generic rules and rule constructors *)

lemma empty_rule_sound [simp]: "sound empty_rule"
by (fastsimp simp add: sound_def)

lemma disj_rule_sound [simp]:
  "sound r1 \<Longrightarrow> sound r2 \<Longrightarrow> sound (disj_rule r1 r2)"
by (fastsimp simp add: sound_def)

lemma disj_rule_list_sound [rule_format, simp]: 
  "(list_all sound rs) \<longrightarrow>  sound (disj_rule_list rs)"
by (induct rs) (clarsimp simp del: empty_rule.simps disj_rule.simps)+


lemma rtranclp_rule_sound_for_induct: 
  "r^** A1 A2
  \<Longrightarrow> satisfiable_abox A2 \<longrightarrow>
  (\<forall>A1 A2. r A1 A2 \<longrightarrow> satisfiable_abox A2 \<longrightarrow> satisfiable_abox A1) \<longrightarrow>
  satisfiable_abox A1"
by (induct rule: rtranclp.induct) auto

lemma rtranclp_rule_sound [simp]: "sound r \<Longrightarrow> sound (r^**)"
by (clarsimp simp add: sound_def rtranclp_rule_sound_for_induct)

lemma tranclp_rule_sound_for_induct:
  "r^++ A1 A2 \<Longrightarrow> 
  satisfiable_abox A2 \<longrightarrow>
  (\<forall>A1 A2. r A1 A2 \<longrightarrow> satisfiable_abox A2 \<longrightarrow> satisfiable_abox A1) \<longrightarrow>
  satisfiable_abox A1"
by (induct rule: tranclp.induct) auto

lemma tranclp_rule_sound [simp]: "sound r \<Longrightarrow> sound (r^++)"
by (clarsimp simp add: sound_def tranclp_rule_sound_for_induct)


  (* Specific rules *)

text {* The following lemmas are not surprising since the rules only add
facts to a sequent. One might show, more in general, that all rules that 
are monotonous in this sense are sound.

It would, of course, be interesting to develop rules that eliminate 
the principal formula from the sequent.
 *}

(* the following is actually a completeness property, 
  see Completeness.thy
lemma and_sound2: 
  " \<lbrakk> Andrule A1 A2; satisfiable_abox A1 \<rbrakk> \<Longrightarrow> satisfiable_abox A2"
  by (fastsimp simp add: andrule_simp satisfiable_abox_def )
*)

lemma and_sound [simp]: "sound Andrule"
  by (fastsimp simp add: sound_def andrule_simp satisfiable_abox_def)

lemma orleft_sound [simp]: "sound Orruleleft"
  by (fastsimp simp add:sound_def orruleleft_simp  satisfiable_abox_def)

lemma orright_sound [simp]: "sound Orruleright"
  by (fastsimp simp add: sound_def orruleright_simp  satisfiable_abox_def)

lemma or_sound [simp]: "sound Orrule"
  by (fastsimp simp add: sound_def orrule_simp  satisfiable_abox_def)

lemma some_sound [simp]: "sound Somerule"
  by (fastsimp simp add: sound_def  somerule_simp  satisfiable_abox_def)

lemma some_gen_sound [simp]: "sound (Somerule_gen gen)"
  by (fastsimp simp add: sound_def  somerule_gen_simp  satisfiable_abox_def)

lemma some3_sound [simp]: "sound Somerule3"
  by (fastsimp simp add: sound_def somerule3_simp  satisfiable_abox_def)

lemma all_sound [simp]: "sound Allrule"
  by (fastsimp simp add: sound_def allrule_simp  satisfiable_abox_def)

lemma alcrule_sound [simp]: "sound alc_rule"
by (simp add: alc_rule_def list_alc_rules_def del: disj_rule_list.simps)

end

