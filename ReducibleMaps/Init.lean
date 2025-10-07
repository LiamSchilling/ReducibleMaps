import Lean

namespace CMaps.Simp

open Lean.Meta

initialize simp_edgeLt_ext : SimpExtension ←
  registerSimpAttr `simp_edgeLt "`edgeLt` reduction lemma"

initialize simp_pathLt_ext : SimpExtension ←
  registerSimpAttr `simp_pathLt "`pathLt` reduction lemma"

initialize simp_pathMem_ext : SimpExtension ←
  registerSimpAttr `simp_pathMem "`pathMem` reduction lemma"

initialize simp_getElem_ext : SimpExtension ←
  registerSimpAttr `simp_getElem "`getElem` reduction lemma"

initialize simp_elemMem_ext : SimpExtension ←
  registerSimpAttr `simp_elemMem "`elemMem` reduction lemma"

initialize simp_contains_ext : SimpExtension ←
  registerSimpAttr `simp_contains "`contains` reduction lemma"

initialize simp_inf_ext : SimpExtension ←
  registerSimpAttr `simp_inf "`inf` reduction lemma"

initialize simp_sup_ext : SimpExtension ←
  registerSimpAttr `simp_sup "`sup` reduction lemma"

initialize simp_infThenSupThenOrdered_ext : SimpExtension ←
  registerSimpAttr `simp_infThenSupThenOrdered "`infThenSupThenOrdered` reduction lemma"

initialize simp_ordered_ext : SimpExtension ←
  registerSimpAttr `simp_ordered "`ordered` reduction lemma"

initialize simp_keyValueLt_ext : SimpExtension ←
  registerSimpAttr `simp_keyValueLt "`keyValueLt` reduction lemma"

end CMaps.Simp
