theory Syntax imports Main

begin

text{* the syntax of ALC  we looking to generalize this formalisation to SHIQ *}
datatype 'nr role = AtomR 'nr

text{* concept definition *}

datatype ('nr, 'nc) concept =
  AtomC 'nc
  |Top  
  |Bottom
  |NotC  "(('nr, 'nc) concept)"
  |AndC  "(('nr, 'nc) concept)" "(('nr, 'nc) concept)"
  |OrC  "(('nr, 'nc) concept)" "(('nr, 'nc) concept)"
  |AllC   "('nr role)" "(('nr, 'nc) concept)"
  |SomeC  "('nr role)" "(('nr, 'nc) concept)"


fun occurs_in :: "(('nr, 'nc) concept) \<Rightarrow> (('nr, 'nc)concept) \<Rightarrow> bool"
where
"occurs_in a b = ((a=b) \<or>
 (case  b of
  NotC c1 \<Rightarrow> (occurs_in a c1)
| AndC c1 c2 \<Rightarrow> (occurs_in a c1) \<or> (occurs_in a c2)
| OrC c1 c2 \<Rightarrow>   (occurs_in a c1) \<or> (occurs_in a c2)
| AllC  r c \<Rightarrow> occurs_in a c
| SomeC r c \<Rightarrow> occurs_in a c
| _ \<Rightarrow> False))"

lemma "occurs_in Top (OrC Top Bottom)"
apply simp
done
lemma "occurs_in Bottom (OrC Top Bottom)"
apply simp
done

end


