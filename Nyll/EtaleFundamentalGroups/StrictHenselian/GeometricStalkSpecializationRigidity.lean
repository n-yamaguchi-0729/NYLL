/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI ChatGPT)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationHomExt
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationMap
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure

/-!
# Rigidity of a chosen geometric-stalk specialization

The base-ring map and the evaluation at the target geometric point determine
an actual map between geometric stalks. The proof first uses uniqueness of
pointed lifts to each original etale neighborhood, then identifies their
maps on global sections with the existing colimit germs.

Unlike germ-extensional uniqueness, agreement on every germ is a conclusion,
not an input. The target pointing field can be arbitrary: uniqueness follows
from the open diagonal and the closed point of the local target spectrum.
No locality of the specialization homomorphism, which need not be local, is assumed.

This is a strict-local compatibility ingredient for Stacks Project,
Section 58.16 (https://stacks.math.columbia.edu/tag/0BUP), not the proper
closed-fibre equivalence or a fundamental-group comparison theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Structure and evaluation characterize the chosen specialization map.
Agreement on germs is derived from actual pointed neighborhood lifts. -/
theorem geometricStalkSpecializationMap_unique_of_structure_evaluation
    {R Ω Ψ : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
    [Field Ψ]
    (s : R →+* Ω) (t : R →+* Ψ)
    (ψ : geometricStalk (Spec.map (CommRingCat.ofHom s)) →+* Ψ)
    (hψ : ψ.comp (geometricStalkStructureMap s) = t)
    (F : geometricStalk (Spec.map (CommRingCat.ofHom s)) ⟶
      geometricStalk (Spec.map (CommRingCat.ofHom t)))
    (hbase : F.hom.comp (geometricStalkStructureMap s) =
      geometricStalkStructureMap t)
    (hevaluation : F ≫ geometricStalkEvaluation (Spec.map (CommRingCat.ofHom t)) =
      CommRingCat.ofHom ψ) :
    F = geometricStalkSpecializationMap s t ψ hψ := by
  apply geometricStalk_hom_ext_of_structure_evaluation s
    (Spec.map (CommRingCat.ofHom t)) F (geometricStalkSpecializationMap s t ψ hψ)
  · exact hbase.trans (geometricStalkSpecializationMap_comp_structure s t ψ hψ).symm
  · exact hevaluation.trans (geometricStalkSpecializationMap_evaluation s t ψ hψ).symm

end EtaleFundamentalGroups.StrictHenselian
