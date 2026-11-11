/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Charts.IsAffineOpenMaximalDomain
public import Nyll.AlgebraicCurves.Models.Charts.FiniteComplIsOpen
public import Nyll.AlgebraicCurves.Models.LocalGeometry.TranscendentalMemRangeStalkIffNe
public import Nyll.AlgebraicCurves.Geometry.Schemes.FunctionFields.OpensRangeAlgebraMapFunctionFieldEqIInf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Proper nonempty opens of smooth proper geometric curves are affine

The existing Riemann--Roch construction supplies a function with a pole at
one specified closed point and no other poles. Summing these functions over
the actual finite complement gives a function with precisely that complement
as its poles: at each omitted point all the other summands lie in its local
ring. The given open is therefore the maximal regular domain of a genuine
transcendental function, so the original finite-map theorem proves affineness.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicCurve

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} [IsIntegral C]
  (c : C ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]

/-- A function whose poles are exactly the actual finite nonempty complement
of the specified open. The construction keeps the original function field
and its literal stalk embeddings. -/
theorem exists_transcendental_mem_stalk_iff_mem_open
    (V : C.Opens) [Nonempty V] (hV : V ≠ ⊤) :
    let _ := (baseToFunctionField c).toAlgebra
    ∃ f : C.functionField, Transcendental k f ∧
      ∀ x : C, f ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range ↔ x ∈ V := by
  classical
  intro kF
  have hVne : (V : Set C).Nonempty :=
    ⟨(Classical.choice (inferInstance : Nonempty V)).val,
      (Classical.choice (inferInstance : Nonempty V)).property⟩
  have hη : genericPoint C ∈ V :=
    ((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr
      (by simpa only [Set.inter_univ, Set.univ_inter] using hVne)
  have hfinite : ((V : Set C)ᶜ).Finite := finite_compl_of_isOpen c V hVne
  let S := hfinite.toFinset
  have hS (x : C) : x ∈ S ↔ x ∉ V := hfinite.mem_toFinset
  have hSnonempty : S.Nonempty := by
    by_contra h
    apply hV
    apply top_unique
    intro x _
    by_contra hx
    exact h ⟨x, (hS x).mpr hx⟩
  have hclosed (q : S) : IsClosed ({q.val} : Set C) :=
    isClosed_singleton_of_ne_genericPoint c q.val
      (fun he => (hS q.val).mp q.property (he.symm ▸ hη))
  have hsingle (q : S) : ∃ f : C.functionField,
      ∀ x : C, f ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range ↔ x ≠ q.val := by
    obtain ⟨f, -, hf⟩ := exists_transcendental_mem_range_stalk_iff_ne c q.val (hclosed q)
    exact ⟨f, hf⟩
  choose f hlocal using hsingle
  let g : C.functionField := ∑ q : S, f q
  have hregular (x : C) (hx : x ∈ V) :
      g ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range := by
    apply Subring.sum_mem
    intro q _
    apply (hlocal q x).mpr
    intro he
    exact (hS q.val).mp q.property (he ▸ hx)
  have hpole (q : S) :
      g ∉ (algebraMap (C.presheaf.stalk q.val) C.functionField).range := by
    intro hg
    have hother : ∑ r ∈ (Finset.univ : Finset S).erase q, f r ∈
        (algebraMap (C.presheaf.stalk q.val) C.functionField).range := by
      apply Subring.sum_mem
      intro r hr
      apply (hlocal r q.val).mpr
      intro he
      exact (Finset.mem_erase.mp hr).1 (Subtype.ext he.symm)
    have hsum : f q + ∑ r ∈ (Finset.univ : Finset S).erase q, f r = g :=
      Finset.add_sum_erase _ _ (Finset.mem_univ q)
    have hf : f q ∈ (algebraMap (C.presheaf.stalk q.val) C.functionField).range := by
      have hsub := (algebraMap (C.presheaf.stalk q.val) C.functionField).range.sub_mem hg hother
      rw [← hsum, add_sub_cancel_right] at hsub
      exact hsub
    exact ((hlocal q q.val).mp hf) rfl
  have hgtr : Transcendental k g := by
    intro halg
    obtain ⟨q, hq⟩ := hSnonempty
    let qS : S := ⟨q, hq⟩
    obtain ⟨v, hv⟩ := exists_place_range_stalk_eq c q (hclosed qS)
    obtain ⟨a, ha⟩ := minpoly.mem_range_of_degree_eq_one k g
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible halg.isIntegral))
    apply hpole qS
    change g ∈ (algebraMap (C.presheaf.stalk q) C.functionField).range
    rw [hv, ← ha]
    exact v.algebraMap_mem' a
  refine ⟨g, hgtr, ?_⟩
  intro x
  constructor
  · intro hx
    by_contra hxV
    exact hpole ⟨x, (hS x).mpr hxV⟩ hx
  · exact hregular x

include c in
/-- Every nonempty proper open of a smooth proper integral curve over an
algebraically closed field is affine, on its original open subscheme. -/
theorem isAffineOpen_of_ne_top_of_isAlgClosed
    (V : C.Opens) [Nonempty V] (hV : V ≠ ⊤) : IsAffineOpen V := by
  let : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
  obtain ⟨f, htr, hlocal⟩ := exists_transcendental_mem_stalk_iff_mem_open c V hV
  have hf : f ∈ (algebraMap Γ(C, V) C.functionField).range := by
    rw [Scheme.Opens.range_algebraMap_functionField_eq_iInf]
    simp only [Subring.mem_iInf]
    exact fun x hx => (hlocal x).mpr hx
  obtain ⟨s, hs⟩ := hf
  have hsection : C.germToFunctionField V s = f := hs
  apply isAffineOpen_of_maximal_domain c V s
  · intro x hx
    rw [hsection] at hx
    exact (hlocal x).mp hx
  · rw [hsection]
    exact htr

include c in
/-- The same affineness theorem for an original open immersion, without
replacing its source by a chosen model of the open. -/
theorem isAffine_of_not_surjective_openImmersion_of_isAlgClosed
    {U : Scheme.{u}} [Nonempty U] (j : U ⟶ C) [IsOpenImmersion j]
    (hj : ¬ Function.Surjective j) : IsAffine U := by
  let V := j.opensRange
  let e : U ≅ V := j.isoOpensRange
  have : Nonempty V := Nonempty.map e.hom inferInstance
  have hV : V ≠ ⊤ := by
    intro h
    apply hj
    intro x
    have hx : x ∈ V := h.symm ▸ (show x ∈ (⊤ : C.Opens) from trivial)
    exact hx
  have : IsAffine V := isAffineOpen_of_ne_top_of_isAlgClosed c V hV
  exact isAffine_of_isAffineHom e.hom

end AlgebraicCurve
