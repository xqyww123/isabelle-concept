theory Concept
  imports Main Performant_Isabelle_ML.Performant_Isabelle_ML
  keywords "concept" :: thy_decl_block
begin

ML_file \<open>undetermined_types.ML\<close>
ML_file \<open>concept_type.ML\<close>

setup \<open>Concept_Type.declare_base\<close>

ML_file \<open>concept_package.ML\<close>

end
