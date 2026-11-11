/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.Ring

/-!
# Faithfully flat descent for subalgebras and scalar extensions
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Subalgebra_faithfullyFlat_of_directed_of_forall_faithfullyFlat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace DirectedFlatDescent
open scoped TensorProduct

universe u v w

theorem _root_.Subalgebra.faithfullyFlat_of_directed_of_forall_faithfullyFlat
    {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H] (K : Subalgebra k H)
    {ι : Type w} [Nonempty ι] (F : ι → Subalgebra k H) (hdir : Directed (· ≤ ·) F)
    (hle : ∀ i, F i ≤ K) (hcov : ∀ x ∈ K, ∃ i, x ∈ F i)
    (hff : ∀ i, Module.FaithfullyFlat ↥(F i) H) :
    Module.FaithfullyFlat ↥K H := by
  classical
  have hfin : ∀ (n : ℕ) (g : Fin n → ↥K), ∃ i, ∀ a, ((g a : ↥K) : H) ∈ F i := by
    intro n g
    choose j hj using fun a => hcov _ (g a).2
    obtain ⟨i, hi⟩ := hdir.finset_le (Finset.univ.image j)
    exact ⟨i, fun a => hi (j a) (Finset.mem_image_of_mem j (Finset.mem_univ a)) (hj a)⟩
  have hfin' : ∀ {α : Type _} [Fintype α] (g : α → ↥K), ∃ i, ∀ a, ((g a : ↥K) : H) ∈ F i := by
    intro α _ g
    obtain ⟨i, hi⟩ := hfin _ (g ∘ (Fintype.equivFin α).symm)
    refine ⟨i, ?_⟩
    intro a
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hi (Fintype.equivFin α a)
  rw [Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top]
  refine ⟨?_, ?_⟩
  · rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
    intro I hI
    obtain ⟨S, hS⟩ := hI
    let g : ↥S → ↥K := fun s => s.1
    have hgI : ∀ s : ↥S, g s ∈ I := fun s => hS ▸ Ideal.subset_span s.2
    obtain ⟨i, hi⟩ := hfin' g
    have : Module.FaithfullyFlat ↥(F i) H := hff i
    have hsurj : ∀ z : ↥I ⊗[↥K] H, ∃ h : ↥S → H, z = ∑ s, (⟨g s, hgI s⟩ : ↥I) ⊗ₜ[↥K] h s := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul m h =>
          have hm : (m : ↥K) ∈ Submodule.span ↥K (Set.range g) := by
            have hr : Set.range g = (↑S : Set ↥K) := by
              ext x; constructor
              · rintro ⟨s, rfl⟩; exact s.2
              · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
            rw [hr]
            change (m : ↥K) ∈ Ideal.span (↑S : Set ↥K)
            rw [hS]; exact m.2
          obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ↥K).mp hm
          refine ⟨fun s => c s • h, ?_⟩
          have hm' : m = ∑ s, c s • (⟨g s, hgI s⟩ : ↥I) := by
            apply Subtype.ext
            rw [← hc]
            simp only [Submodule.coe_sum, Submodule.coe_smul]
          rw [hm', TensorProduct.sum_tmul]
          exact Finset.sum_congr rfl fun s _ => by rw [TensorProduct.smul_tmul]
      | add z₁ z₂ h₁ h₂ =>
          obtain ⟨f₁, rfl⟩ := h₁
          obtain ⟨f₂, rfl⟩ := h₂
          refine ⟨f₁ + f₂, ?_⟩
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun s _ => by rw [Pi.add_apply, TensorProduct.tmul_add]
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨h, rfl⟩ := hsurj z
    have hrel : ∑ s, ((g s : ↥K) : H) * h s = 0 := by
      rw [map_sum] at hz
      change (∑ s, ((g s : ↥K) : H) * h s) = 0 at hz
      exact hz
    let g' : ↥S → ↥(F i) := fun s => ⟨(g s : H), hi s⟩
    let J : Ideal ↥(F i) := Ideal.span (Set.range g')
    have hJ : J.FG := ⟨Finset.univ.image g', by
      simp only [J, Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
    have hinjJ := Module.Flat.iff_lift_lsmul_comp_subtype_injective.mp
      (inferInstance : Module.Flat ↥(F i) H) hJ
    let z' : ↥J ⊗[↥(F i)] H := ∑ s, (⟨g' s, Ideal.subset_span ⟨s, rfl⟩⟩ : ↥J) ⊗ₜ[↥(F i)] h s
    have hz' : z' = 0 := by
      apply hinjJ
      rw [map_zero, map_sum]
      change (∑ s, ((g s : ↥K) : H) * h s) = 0
      exact hrel
    have hJI : ∀ j : ↥(F i), j ∈ J → (Subalgebra.inclusion (hle i) j) ∈ I := by
      intro j hj
      induction hj using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨s, rfl⟩ := hx
          have : Subalgebra.inclusion (hle i) (g' s) = g s := Subtype.ext rfl
          rw [this]; exact hgI s
      | zero => rw [map_zero]; exact I.zero_mem
      | add x y _ _ hx hy => rw [map_add]; exact I.add_mem hx hy
      | smul r x _ hx => rw [smul_eq_mul, map_mul]; exact I.mul_mem_left _ hx
    let θ₀ : ↥J →+ H →+ ↥I ⊗[↥K] H :=
      { toFun := fun j =>
          { toFun := fun x => (⟨Subalgebra.inclusion (hle i) (j : ↥(F i)), hJI _ j.2⟩ : ↥I) ⊗ₜ[↥K] x
            map_zero' := TensorProduct.tmul_zero _ _
            map_add' := fun x y => TensorProduct.tmul_add _ x y }
        map_zero' := by
          ext x
          simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.zero_apply]
          have : (⟨Subalgebra.inclusion (hle i) ((0 : ↥J) : ↥(F i)), hJI _ (0 : ↥J).2⟩ : ↥I) = 0 :=
            Subtype.ext (map_zero _)
          rw [this, TensorProduct.zero_tmul]
        map_add' := fun j j' => by
          ext x
          simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply, ←
              TensorProduct.add_tmul]
          congr 1 }
    let θ : ↥J ⊗[↥(F i)] H →+ ↥I ⊗[↥K] H := TensorProduct.liftAddHom θ₀ (by
      intro r j x
      change (⟨Subalgebra.inclusion (hle i) ((r • j : ↥J) : ↥(F i)), _⟩ : ↥I) ⊗ₜ[↥K] x
        = (⟨Subalgebra.inclusion (hle i) (j : ↥(F i)), _⟩ : ↥I) ⊗ₜ[↥K] (r • x)
      have e1 : (⟨Subalgebra.inclusion (hle i) ((r • j : ↥J) : ↥(F i)), hJI _ (r • j).2⟩ : ↥I)
          = (Subalgebra.inclusion (hle i) r) • (⟨Subalgebra.inclusion (hle i) (j : ↥(F i)), hJI _
              j.2⟩ : ↥I) := by
        apply Subtype.ext
        change Subalgebra.inclusion (hle i) (r * (j : ↥(F i))) = Subalgebra.inclusion (hle i) r * _
        exact map_mul _ _ _
      rw [e1, TensorProduct.smul_tmul]
      rfl)
    have hθ : ∀ s, θ ((⟨g' s, Ideal.subset_span ⟨s, rfl⟩⟩ : ↥J) ⊗ₜ[↥(F i)] h s)
        = (⟨g s, hgI s⟩ : ↥I) ⊗ₜ[↥K] h s := by
      intro s
      rw [TensorProduct.liftAddHom_tmul]
      change (⟨Subalgebra.inclusion (hle i) (g' s), _⟩ : ↥I) ⊗ₜ[↥K] h s = _
      congr 1
    calc (∑ s, (⟨g s, hgI s⟩ : ↥I) ⊗ₜ[↥K] h s) = θ z' := by
          rw [map_sum]; exact Finset.sum_congr rfl fun s _ => (hθ s).symm
      _ = 0 := by rw [hz', map_zero]
  · intro I hI1
    have h1 : (1 : H) ∈ I.map (algebraMap ↥K H) := by
      have : (1 : H) ∈ I • (⊤ : Submodule ↥K H) := by rw [hI1]; exact Submodule.mem_top
      rw [Ideal.smul_top_eq_map] at this
      exact this
    obtain ⟨n, x, m₀, hsum⟩ := Submodule.mem_span_set'.mp h1
    have hm₀ : ∀ t, ∃ m ∈ I, (m₀ t : H) = algebraMap ↥K H m := fun t => by
      obtain ⟨m, hm, hmt⟩ := (m₀ t).2
      exact ⟨m, hm, hmt.symm⟩
    choose m hmI hm using hm₀
    obtain ⟨i, hi⟩ := hfin n m
    have : Module.FaithfullyFlat ↥(F i) H := hff i
    let m' : Fin n → ↥(F i) := fun t => ⟨(m t : H), hi t⟩
    let J : Ideal ↥(F i) := Ideal.span (Set.range m')
    have hJ1 : J • (⊤ : Submodule ↥(F i) H) = ⊤ := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff, Ideal.eq_top_iff_one, ← hsum]
      refine Submodule.sum_mem _ fun t _ => ?_
      rw [smul_eq_mul]
      refine Ideal.mul_mem_left _ _ ?_
      rw [hm t]
      have : algebraMap ↥K H (m t) = algebraMap ↥(F i) H (m' t) := rfl
      rw [this]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨t, rfl⟩)
    have hJ : J = ⊤ := ((Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top _ _).mp (hff i)).2 J
        hJ1
    have h1J : (1 : ↥(F i)) ∈ J := by rw [hJ]; trivial
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1J
    rw [Ideal.eq_top_iff_one]
    have : (1 : ↥K) = ∑ t, Subalgebra.inclusion (hle i) (c t) * m t := by
      apply Subtype.ext
      have := congrArg (fun y : ↥(F i) => (y : H)) hc
      simp only [Subalgebra.coe_one] at this
      rw [Subalgebra.coe_one, ← this]
      change (F i).val (∑ t, c t * m' t) =
        K.val (∑ t, Subalgebra.inclusion (hle i) (c t) * m t)
      rw [map_sum, map_sum]
      exact Finset.sum_congr rfl fun _ _ => rfl
    rw [this]
    exact I.sum_mem fun t _ => I.mul_mem_left _ (hmI t)

end DirectedFlatDescent
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Subalgebra_faithfullyFlat_of_faithfullyFlat_range_baseChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace BaseChangeFlatDescent
open scoped TensorProduct

universe u v w

namespace S17Ta

universe u₁ u₂ u₃

section Descent

variable (R : Type u₁) [CommRing R] (S : Type u₂) [CommRing S] [Algebra R S]
variable (M : Type u₃) [AddCommGroup M] [Module R M]

/-- The cancellation equivalence for two scalar-extended tensor factors. -/
noncomputable def cancelIso (N : Type*) [AddCommGroup N] [Module R N] :
    (S ⊗[R] M) ⊗[S] (S ⊗[R] N) ≃ₗ[S] S ⊗[R] (M ⊗[R] N) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S (S ⊗[R] M) N).trans
    (TensorProduct.AlgebraTensorModule.assoc R R S S M N)

theorem cancelIso_tmul {N : Type*} [AddCommGroup N] [Module R N] (s s' : S) (m : M) (n : N) :
    cancelIso R S M N ((s ⊗ₜ[R] m) ⊗ₜ[S] (s' ⊗ₜ[R] n)) = (s' * s) ⊗ₜ[R] (m ⊗ₜ[R] n) := by
  simp only [cancelIso, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.AlgebraTensorModule.assoc_tmul, TensorProduct.smul_tmul', smul_eq_mul]

theorem cancelIso_naturality {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup
    N'] [Module R N']
    (f : N →ₗ[R] N') (z : (S ⊗[R] M) ⊗[S] (S ⊗[R] N)) :
    cancelIso R S M N' (((f.baseChange S).lTensor (S ⊗[R] M)) z)
      = (f.lTensor M).lTensor S (cancelIso R S M N z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      induction x using TensorProduct.inductionOn with
      | add x₁ x₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
      | tmul s m =>
          induction y using TensorProduct.inductionOn with
          | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
          | tmul s' n =>
              rw [LinearMap.lTensor_tmul, LinearMap.baseChange_tmul, cancelIso_tmul, cancelIso_tmul,
                LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]

theorem faithfullyFlat_of_faithfullyFlat_baseChange [Module.FaithfullyFlat R S]
    [Module.FaithfullyFlat S (S ⊗[R] M)] : Module.FaithfullyFlat R M := by
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
  constructor
  · rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
    intro N N' _ _ _ _ f hf
    rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective R S]
    have hfS : Function.Injective (f.baseChange S) :=
        Module.Flat.lTensor_preserves_injective_linearMap f hf
    have hg : Function.Injective ((f.baseChange S).lTensor (S ⊗[R] M)) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hfS
    have hcomp : ((f.lTensor M).lTensor S : S ⊗[R] (M ⊗[R] N) → S ⊗[R] (M ⊗[R] N'))
        = (cancelIso R S M N') ∘ ((f.baseChange S).lTensor (S ⊗[R] M)) ∘ (cancelIso R S M N).symm
            := by
      funext z
      simp only [Function.comp_apply]
      rw [cancelIso_naturality, LinearEquiv.apply_symm_apply]
    rw [hcomp]
    exact (cancelIso R S M N').injective.comp (hg.comp (cancelIso R S M N).symm.injective)
  · intro I hI hIM
    let J : Ideal S := I.map (algebraMap R S)
    have hJ : J ≠ ⊤ := by
      intro hJ
      have h1 := ((Module.FaithfullyFlat.iff_flat_and_proper_ideal R S).mp inferInstance).2 I hI
      apply h1
      have hJ' : Ideal.map (algebraMap R S) I = ⊤ := hJ
      rw [Ideal.smul_top_eq_map, hJ']
      rfl
    have h2 := ((Module.FaithfullyFlat.iff_flat_and_proper_ideal S (S ⊗[R] M)).mp inferInstance).2
        J hJ
    apply h2
    have hone : ∀ m : M, (1 : S) ⊗ₜ[R] m ∈ J • (⊤ : Submodule S (S ⊗[R] M)) := by
      intro m
      have hm : m ∈ I • (⊤ : Submodule R M) := by rw [hIM]; exact Submodule.mem_top
      refine Submodule.smul_induction_on hm ?_ ?_
      · intro i hi n _
        have : (1 : S) ⊗ₜ[R] (i • n) = (algebraMap R S i) • ((1 : S) ⊗ₜ[R] n) := by
          rw [TensorProduct.tmul_smul, algebraMap_smul]
        rw [this]
        exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hi) Submodule.mem_top
      · intro x y hx hy
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ hx hy
    rw [eq_top_iff]
    rintro z -
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul s m =>
        have : s ⊗ₜ[R] m = s • ((1 : S) ⊗ₜ[R] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul,
            mul_one]
        rw [this]
        exact Submodule.smul_mem _ s (hone m)

end Descent

end S17Ta

namespace S17Ta

section Plumbing

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H] (K : Subalgebra k H)
variable (k' : Type w) [Field k'] [Algebra k k']

/-- The map induced by inclusion of a subalgebra after extending the base field. -/
noncomputable abbrev φ : k' ⊗[k] ↥K →ₐ[k'] k' ⊗[k] H := Algebra.TensorProduct.map (AlgHom.id k' k')
    K.val

/-- The image of the subalgebra after extending the base field. -/
noncomputable abbrev K' : Subalgebra k' (k' ⊗[k] H) := (φ K k').range

theorem φ_tmul (c : k') (x : ↥K) : φ K k' (c ⊗ₜ[k] x) = c ⊗ₜ[k] (x : H) := by
  rw [Algebra.TensorProduct.map_tmul]; rfl

theorem tmul_mem (c : k') {y : H} (hy : y ∈ K) : c ⊗ₜ[k] y ∈ K' K k' :=
  ⟨c ⊗ₜ[k] ⟨y, hy⟩, φ_tmul K k' c ⟨y, hy⟩⟩

/-- The original subalgebra embedded in its base-changed image. -/
noncomputable def ι : ↥K →ₐ[k] ↥(K' K k') :=
  (((φ K k').rangeRestrict).restrictScalars k).comp Algebra.TensorProduct.includeRight

theorem ι_apply_coe (x : ↥K) : ((ι K k' x : ↥(K' K k')) : k' ⊗[k] H) = (1 : k') ⊗ₜ[k] (x : H) := by
  change φ K k' ((1 : k') ⊗ₜ[k] x) = _
  exact φ_tmul K k' 1 x

end Plumbing

end S17Ta

open S17Ta in
theorem _root_.Subalgebra.faithfullyFlat_of_faithfullyFlat_range_baseChange
    {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H] (K : Subalgebra k H)
    (k' : Type w) [Field k'] [Algebra k k']
    (hff : Module.FaithfullyFlat
      ↥((Algebra.TensorProduct.map (AlgHom.id k' k') K.val).range) (k' ⊗[k] H)) :
    Module.FaithfullyFlat ↥K H := by
  classical
  have : Module.FaithfullyFlat ↥(K' K k') (k' ⊗[k] H) := hff
  let algKK' : Algebra ↥K ↥(K' K k') := (ι K k').toRingHom.toAlgebra
  have hsmulK' : ∀ (x : ↥K) (κ : ↥(K' K k')), x • κ = ι K k' x * κ := fun _ _ => rfl
  have towerk : IsScalarTower k ↥K ↥(K' K k') := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    apply Subtype.ext
    change algebraMap k (k' ⊗[k] H) c = ((ι K k' (algebraMap k ↥K c) : ↥(K' K k')) : k' ⊗[k] H)
    rw [ι_apply_coe, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
      Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let g : ↥K →ₗ[↥K] k' →ₗ[k] ↥(K' K k') :=
    LinearMap.mk₂' ↥K k (fun x c => ⟨c ⊗ₜ[k] (x : H), tmul_mem K k' c x.2⟩)
      (fun x y c => Subtype.ext (by
        change c ⊗ₜ[k] ((x + y : ↥K) : H) = c ⊗ₜ[k] (x : H) + c ⊗ₜ[k] (y : H)
        rw [Subalgebra.coe_add, TensorProduct.tmul_add]))
      (fun y x c => Subtype.ext (by
        change c ⊗ₜ[k] ((y • x : ↥K) : H) = ((ι K k' y * ⟨c ⊗ₜ[k] (x : H), tmul_mem K k' c x.2⟩ :
            ↥(K' K k')) : k' ⊗[k] H)
        rw [Subalgebra.coe_mul, ι_apply_coe, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
            smul_eq_mul,
          Subalgebra.coe_mul]))
      (fun x c₁ c₂ => Subtype.ext (by
        change (c₁ + c₂) ⊗ₜ[k] (x : H) = c₁ ⊗ₜ[k] (x : H) + c₂ ⊗ₜ[k] (x : H)
        rw [TensorProduct.add_tmul]))
      (fun a x c => Subtype.ext (by
        change (a • c) ⊗ₜ[k] (x : H) = a • (c ⊗ₜ[k] (x : H))
        rw [TensorProduct.smul_tmul']))
  let f : ↥K ⊗[k] k' →ₗ[↥K] ↥(K' K k') := TensorProduct.AlgebraTensorModule.lift g
  have hf : ∀ (x : ↥K) (c : k'), f (x ⊗ₜ[k] c) = ⟨c ⊗ₜ[k] (x : H), tmul_mem K k' c x.2⟩ := fun x c
      => by
    rw [TensorProduct.AlgebraTensorModule.lift_tmul]; rfl
  have hfsurj : Function.Surjective f := by
    have key : ∀ t : k' ⊗[k] ↥K, ∃ s, f s = ⟨φ K k' t, t, rfl⟩ := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul c x => exact ⟨x ⊗ₜ[k] c, by rw [hf]; exact Subtype.ext (φ_tmul K k' c x).symm⟩
      | add t₁ t₂ h₁ h₂ =>
          obtain ⟨s₁, hs₁⟩ := h₁
          obtain ⟨s₂, hs₂⟩ := h₂
          exact ⟨s₁ + s₂, by
            rw [map_add, hs₁, hs₂]
            exact Subtype.ext (show φ K k' t₁ + φ K k' t₂ = φ K k' (t₁ + t₂) by rw [map_add])⟩
    rintro ⟨y, t, rfl⟩
    obtain ⟨s, hs⟩ := key t
    exact ⟨s, hs⟩
  have hfval : ∀ s, ((f s : ↥(K' K k')) : k' ⊗[k] H)
      = (K.val.toLinearMap.lTensor k') (TensorProduct.comm k ↥K k' s) := by
    intro s
    induction s using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, Subalgebra.coe_add, hx, hy, map_add, map_add]
    | tmul x c => rw [hf, TensorProduct.comm_tmul, LinearMap.lTensor_tmul]; rfl
  have hfinj : Function.Injective f := by
    intro s₁ s₂ h
    have h' : ((f s₁ : ↥(K' K k')) : k' ⊗[k] H) = f s₂ := congrArg Subtype.val h
    rw [hfval, hfval] at h'
    exact (TensorProduct.comm k ↥K k').injective
      (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective h')
  let e : ↥K ⊗[k] k' ≃ₗ[↥K] ↥(K' K k') := LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  have : Module.FaithfullyFlat ↥K ↥(K' K k') := Module.FaithfullyFlat.of_linearEquiv ↥K (↥K ⊗[k]
      k') e.symm
  let modKH' : Module ↥K (k' ⊗[k] H) := Module.compHom (k' ⊗[k] H) (ι K k').toRingHom
  have hsmulH' : ∀ (x : ↥K) (z : k' ⊗[k] H), x • z = ((ι K k' x : ↥(K' K k')) : k' ⊗[k] H) * z :=
      fun _ _ => rfl
  have : IsScalarTower ↥K ↥(K' K k') (k' ⊗[k] H) :=
    ⟨fun x κ z => by
      change (((ι K k' x * κ : ↥(K' K k')) : k' ⊗[k] H)) * z = ((ι K k' x : ↥(K' K k')) : k' ⊗[k]
          H) * ((κ : k' ⊗[k] H) * z)
      rw [Subalgebra.coe_mul, mul_assoc]⟩
  let g' : ↥(K' K k') →ₗ[↥(K' K k')] H →ₗ[↥K] (k' ⊗[k] H) :=
    LinearMap.mk₂' ↥(K' K k') ↥K (fun κ h => (κ : k' ⊗[k] H) * ((1 : k') ⊗ₜ[k] h))
      (fun κ₁ κ₂ h => by rw [Subalgebra.coe_add, add_mul])
      (fun κ' κ h => by
        change ((κ' * κ : ↥(K' K k')) : k' ⊗[k] H) * _ = (κ' : k' ⊗[k] H) * ((κ : k' ⊗[k] H) * _)
        rw [Subalgebra.coe_mul, mul_assoc])
      (fun κ h₁ h₂ => by rw [TensorProduct.tmul_add, mul_add])
      (fun x κ h => by
        change (κ : k' ⊗[k] H) * ((1 : k') ⊗ₜ[k] ((x : H) * h)) = ((ι K k' x : ↥(K' K k')) : k'
            ⊗[k] H) * ((κ : k' ⊗[k] H) * _)
        rw [ι_apply_coe, ← mul_one (1 : k'), ← Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        ring)
  let Φ₀ : ↥(K' K k') ⊗[↥K] H →ₗ[↥(K' K k')] (k' ⊗[k] H) := TensorProduct.AlgebraTensorModule.lift
      g'
  have hΦ₀ : ∀ (κ : ↥(K' K k')) (h : H), Φ₀ (κ ⊗ₜ[↥K] h) = (κ : k' ⊗[k] H) * ((1 : k') ⊗ₜ[k] h) :=
      fun κ h => by
    rw [TensorProduct.AlgebraTensorModule.lift_tmul]; rfl
  have hΦ₀surj : Function.Surjective Φ₀ := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    rintro z -
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul c h =>
        refine ⟨(⟨c ⊗ₜ[k] (1 : H), tmul_mem K k' c K.one_mem⟩ : ↥(K' K k')) ⊗ₜ[↥K] h, ?_⟩
        rw [hΦ₀]
        change (c ⊗ₜ[k] (1 : H)) * ((1 : k') ⊗ₜ[k] h) = c ⊗ₜ[k] h
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let cK : k' → ↥(K' K k') := fun c => ⟨c ⊗ₜ[k] (1 : H), tmul_mem K k' c K.one_mem⟩
  have cK_zero : cK 0 = 0 := Subtype.ext (TensorProduct.zero_tmul _ (1 : H))
  have cK_add : ∀ c₁ c₂, cK (c₁ + c₂) = cK c₁ + cK c₂ := fun c₁ c₂ => Subtype.ext
      (TensorProduct.add_tmul c₁ c₂ (1 : H))
  let ψ₂ : k' →+ H →+ (↥(K' K k') ⊗[↥K] H) :=
    { toFun := fun c => (TensorProduct.mk ↥K ↥(K' K k') H (cK c)).toAddMonoidHom
      map_zero' := by
        ext h
        change cK 0 ⊗ₜ[↥K] h = 0
        rw [cK_zero, TensorProduct.zero_tmul]
      map_add' := fun c₁ c₂ => by
        ext h
        change cK (c₁ + c₂) ⊗ₜ[↥K] h = cK c₁ ⊗ₜ[↥K] h + cK c₂ ⊗ₜ[↥K] h
        rw [cK_add, TensorProduct.add_tmul] }
  have cK_smul : ∀ (a : k) (c : k'), (algebraMap k ↥K a) • cK c = cK (a • c) := by
    intro a c
    apply Subtype.ext
    change ((ι K k' (algebraMap k ↥K a) : ↥(K' K k')) : k' ⊗[k] H) * (c ⊗ₜ[k] (1 : H)) = (a • c)
        ⊗ₜ[k] (1 : H)
    rw [TensorProduct.smul_tmul, ι_apply_coe, Subalgebra.coe_algebraMap,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one, Algebra.algebraMap_eq_smul_one]
  let Ψ : k' ⊗[k] H →+ (↥(K' K k') ⊗[↥K] H) := TensorProduct.liftAddHom ψ₂ (fun a c h => by
    change cK (a • c) ⊗ₜ[↥K] h = cK c ⊗ₜ[↥K] (a • h)
    have e1 : ((algebraMap k ↥K a) • cK c) ⊗ₜ[↥K] h = cK c ⊗ₜ[↥K] ((algebraMap k ↥K a) • h) :=
      TensorProduct.smul_tmul _ _ _
    have e2 : (algebraMap k ↥K a) • h = a • h := algebraMap_smul (↥K) a h
    rw [← e2, ← e1, cK_smul])
  have hΨ : ∀ (c : k') (h : H), Ψ (c ⊗ₜ[k] h) = cK c ⊗ₜ[↥K] h := fun c h =>
    TensorProduct.liftAddHom_tmul _ _ _ _
  have hL : ∀ (t : k' ⊗[k] ↥K) (h : H),
      Ψ (φ K k' t * ((1 : k') ⊗ₜ[k] h)) = (⟨φ K k' t, t, rfl⟩ : ↥(K' K k')) ⊗ₜ[↥K] h := by
    intro t h
    induction t using TensorProduct.inductionOn with
    | tmul c x =>
        have h1 : (⟨φ K k' (c ⊗ₜ[k] x), c ⊗ₜ[k] x, rfl⟩ : ↥(K' K k')) = x • cK c := by
          apply Subtype.ext
          change φ K k' (c ⊗ₜ[k] x) = ((ι K k' x : ↥(K' K k')) : k' ⊗[k] H) * (c ⊗ₜ[k] (1 : H))
          rw [φ_tmul, ι_apply_coe, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        rw [h1, φ_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hΨ, TensorProduct.smul_tmul]
        rfl
    | add t₁ t₂ h₁ h₂ =>
        have h2 : (⟨φ K k' (t₁ + t₂), t₁ + t₂, rfl⟩ : ↥(K' K k'))
            = ⟨φ K k' t₁, t₁, rfl⟩ + ⟨φ K k' t₂, t₂, rfl⟩ := Subtype.ext (map_add _ _ _)
        rw [h2, TensorProduct.add_tmul, map_add, add_mul, map_add, h₁, h₂]
  have hΨΦ : ∀ w, Ψ (Φ₀ w) = w := by
    intro w
    induction w using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul κ h =>
        obtain ⟨t, ht⟩ := κ.2
        have hκ : κ = ⟨φ K k' t, t, rfl⟩ := Subtype.ext ht.symm
        rw [hκ, hΦ₀]
        exact hL t h
  have hΦ₀inj : Function.Injective Φ₀ := fun w₁ w₂ h => by
    rw [← hΨΦ w₁, ← hΨΦ w₂, h]
  let Φ : ↥(K' K k') ⊗[↥K] H ≃ₗ[↥(K' K k')] (k' ⊗[k] H) := LinearEquiv.ofBijective Φ₀ ⟨hΦ₀inj,
      hΦ₀surj⟩
  have : Module.FaithfullyFlat ↥(K' K k') (↥(K' K k') ⊗[↥K] H) :=
    Module.FaithfullyFlat.of_linearEquiv ↥(K' K k') (k' ⊗[k] H) Φ
  exact faithfullyFlat_of_faithfullyFlat_baseChange ↥K ↥(K' K k') H

end BaseChangeFlatDescent
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Module_Flat_of_flat_of_faithfullyFlat_right.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace FaithfullyFlatDescent
open TensorProduct
namespace Module
open _root_.Module
namespace Flat
open _root_.Module.Flat
end Module.Flat

theorem Module.Flat.of_flat_of_faithfullyFlat_right_aux (R S T : Type*) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.FaithfullyFlat S T] [Module.Flat R T] : Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  rw [← LinearMap.baseChange_eq_lTensor,
    ← Module.FaithfullyFlat.lTensor_injective_iff_injective S T]
  have key : ∀ x, TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T P
      (((f.baseChange S).lTensor T) x) =
      f.lTensor T (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul t y =>
      induction y using TensorProduct.inductionOn with
      | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
      | tmul s n =>
        simp only [LinearMap.lTensor_tmul, LinearMap.baseChange_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  have hT : Function.Injective (f.lTensor T) := Module.Flat.lTensor_preserves_injective_linearMap f
      hf
  have : Function.Injective (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T P ∘
      ((f.baseChange S).lTensor T)) := by
    rw [show (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T P ∘
        ((f.baseChange S).lTensor T) : _ → _) =
        f.lTensor T ∘ TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N from funext key]
    exact hT.comp (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N).injective
  exact this.of_comp

theorem _root_.Module.Flat.of_flat_of_faithfullyFlat_right (R S T : Type*) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.FaithfullyFlat S T] [Module.Flat R T] : Module.Flat R S :=
  Module.Flat.of_flat_of_faithfullyFlat_right_aux R S T

end FaithfullyFlatDescent
end NOSProofs
end AbelianVarieties
end
