theory Codegen imports Implementation


begin
    (*constdefs "my_rule_app  \<equiv> apply_srule and_rule" *)
term new_var
constdefs my_new_var :: "nat list \<Rightarrow> nat"
  "my_new_var vs \<equiv> (Suc (list_max vs))"
export_code my_new_var dfs in OCaml file "Generated/prover.ml"



end

