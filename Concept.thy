theory Concept
  imports Main Performant_Isabelle_ML.Performant_Isabelle_ML
  keywords "concept" :: thy_decl_block
begin

ML_file \<open>undetermined_types.ML\<close>
ML_file \<open>concept_type.ML\<close>

setup \<open>Concept_Type.declare_base\<close>

ML_file \<open>concept_package.ML\<close>
ML_file \<open>concept_intro_table.ML\<close>
ML_file \<open>concept_search.ML\<close>
ML_file \<open>concept_fact.ML\<close>

text \<open>An implication and a bounded quantification at the head of a conclusion are opened by
  extraction rules: what they add as a premise stays on what is taken out.\<close>

declare mp [concept_extraction] and bspec [concept_extraction]

end
