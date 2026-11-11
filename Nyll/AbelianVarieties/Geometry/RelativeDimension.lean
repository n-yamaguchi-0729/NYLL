/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawSmoothOfRelativeDimension
public import Nyll.AbelianVarieties.Geometry.GroupLaw
public import Nyll.AbelianVarieties.NeronModels.Endomorphisms
public import Nyll.SchemeTheory.Morphisms.SmoothnessCriteria
public import Nyll.AbelianVarieties.Basic
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Action
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.RelativeGroupLawGrpObj

/-! # Smoothness and relative dimension of group schemes -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_geometricallyReduced_of_locallyOfFiniteType.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace GoodReductionJacobian.RelativeGroupLaw

open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian

universe u

/-- Geometrically reduced finite-type group schemes over a field are smooth. -/
theorem smooth_of_geometricallyReduced_of_locallyOfFiniteType
    {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    [GeometricallyReduced f] [LocallyOfFiniteType f] (G : RelativeGroupLaw K f) :
    Smooth f := by
  let : GrpObj (Over.mk f) := G.grpObjOverMk
  exact smooth_of_grpObj f

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

/-- A smooth group scheme over a field has constant relative dimension. -/
theorem exists_smoothOfRelativeDimension_of_smooth
    {K : Type u} [Field K] {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of K)} [Smooth g]
    (L : RelativeGroupLaw K g) :
    ∃ d : ℕ, SmoothOfRelativeDimension d g :=
  L.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_isPullback_action_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace GoodReductionJacobian.RelativeGroupLaw

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

/-- A flat quotient by a smooth subgroup has the expected relative dimension. -/
theorem smoothOfRelativeDimension_of_isPullback_action_of_surjective
    (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} [Nonempty N] (i : N ⟶ G) [IsClosedImmersion i]
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    {Q : Scheme.{u}} (fQ : Q ⟶ Spec (CommRingCat.of k)) (q : G ⟶ Q) (hq : q ≫ fQ = f)
    [Flat q] [LocallyOfFinitePresentation q] [Surjective q] [QuasiCompact q]
    (hR : IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f) (L.action i) q q) :
    SmoothOfRelativeDimension h q ∧ SmoothOfRelativeDimension (g - h) fQ ∧ h ≤ g := by
  have hbc : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension h) :=
    smoothOfRelativeDimension_isStableUnderBaseChange h
  have h1 : SmoothOfRelativeDimension h (pullback.snd (i ≫ f) f) :=
    hbc.of_isPullback (IsPullback.of_hasPullback (i ≫ f) f) inferInstance
  have hq' : SmoothOfRelativeDimension h q :=
    AlgebraicGeometry.SmoothOfRelativeDimension.of_isPullback_of_flat_of_surjective h hR
  have : Nonempty G := Nonempty.map i.base inferInstance
  have : SmoothOfRelativeDimension g (q ≫ fQ) := by rw [hq]; infer_instance
  have : SmoothOfRelativeDimension h q := hq'
  obtain ⟨hQ, hle⟩ :=
    AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_of_surjective_of_field fQ q g h
  exact ⟨hq', hQ, hle⟩

end GoodReductionJacobian.RelativeGroupLaw
end
