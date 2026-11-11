/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Antipodes and translations of commutative Hopf algebras

The antipode is involutive, translations are invertible, and they transport augmentation ideals.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_antipode_antipode.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.Reduction_Support_HopfAlgebra_AntipodeAntipode

open _root_.Coalgebra
open _root_.HopfAlgebra
open scoped TensorProduct
open scoped Coalgebra.TensorProduct

namespace HopfAlgebra
open _root_.HopfAlgebra
open _root_.HopfAlgebra

section GeneralHopf
variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [HopfAlgebra R A]

private theorem antipode_algebraMap' (r : R) :
    antipode R (algebraMap R A r) = algebraMap R A r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, antipode_one]

private theorem toConv_antipode_mul_toConv_id' :
    WithConv.toConv (antipode R (A := A)) * WithConv.toConv (LinearMap.id : A →ₗ[R] A)
      = (1 : WithConv (A →ₗ[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.id_coe, id_eq]
  exact sum_antipode_mul_eq_algebraMap_counit (ℛ R a)

end GeneralHopf

section CommutativeHopf
variable {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [HopfAlgebra R A]

private theorem sum_antipode_antipode_mul_antipode' {a : A} {ι𝓡 : Type*}
    (𝓡 : Coalgebra.Repr R a ι𝓡) :
    ∑ i ∈ 𝓡.index, antipode R (antipode R (𝓡.left i)) * antipode R (𝓡.right i)
      = algebraMap R A (counit (R := R) a) := by
  calc ∑ i ∈ 𝓡.index, antipode R (antipode R (𝓡.left i)) * antipode R (𝓡.right i)
      = ∑ i ∈ 𝓡.index, antipode R (antipode R (𝓡.left i) * 𝓡.right i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [antipode_mul_antidistrib (antipode R (𝓡.left i)) (𝓡.right i)]
        exact mul_comm _ _
    _ = antipode R (∑ i ∈ 𝓡.index, antipode R (𝓡.left i) * 𝓡.right i) := by
        rw [map_sum]
    _ = antipode R (algebraMap R A (counit (R := R) a)) := by
        rw [sum_antipode_mul_eq_algebraMap_counit 𝓡]
    _ = algebraMap R A (counit (R := R) a) := antipode_algebraMap' _

private theorem toConv_antipode_comp_antipode_mul_toConv_antipode' :
    WithConv.toConv (antipode R ∘ₗ antipode R : A →ₗ[R] A)
        * WithConv.toConv (antipode R (A := A))
      = (1 : WithConv (A →ₗ[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply]
  exact sum_antipode_antipode_mul_antipode' (ℛ R a)

private theorem antipode_comp_antipode' :
    (antipode R ∘ₗ antipode R : A →ₗ[R] A) = LinearMap.id :=
  WithConv.toConv_injective
    (left_inv_eq_right_inv toConv_antipode_comp_antipode_mul_toConv_antipode'
      toConv_antipode_mul_toConv_id')

end CommutativeHopf
end HopfAlgebra

theorem _root_.HopfAlgebra.antipode_antipode {R : Type*} [CommSemiring R]
    {A : Type*} [CommSemiring A] [HopfAlgebra R A] (a : A) :
    HopfAlgebra.antipode R (HopfAlgebra.antipode R a) = a := by
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
    LinearMap.congr_fun (HopfAlgebra.antipode_comp_antipode' (R := R) (A := A)) a

end AbelianVarieties.NOSProofs.Reduction_Support_HopfAlgebra_AntipodeAntipode
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.HopfTranslation

open scoped TensorProduct

universe u v w

namespace S17Tc1

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]

/-- Linear translation by a rational point. -/
noncomputable def T (g : H →ₐ[k] k) : H →ₗ[k] H :=
  (TensorProduct.lid k H).toLinearMap ∘ₗ LinearMap.rTensor H g.toLinearMap ∘ₗ Coalgebra.comul

theorem T_apply (g : H →ₐ[k] k) (h : H) :
    T g h =
      TensorProduct.lid k H (LinearMap.rTensor H g.toLinearMap (Coalgebra.comul (R := k) h)) := rfl

theorem lid_map_eq (g : H →ₐ[k] k) (z : H ⊗[k] H) :
    Algebra.TensorProduct.lid k H (Algebra.TensorProduct.map g (AlgHom.id k H) z) =
      TensorProduct.lid k H (LinearMap.rTensor H g.toLinearMap z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul,
      LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul, AlgHom.toLinearMap_apply, AlgHom.coe_id, id_eq]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The canonical antipode as an algebra morphism. -/
noncomputable def Sₐ : H →ₐ[k] H := HopfAlgebra.antipodeAlgHom k H

@[scoped simp] theorem Sₐ_apply (h : H) : Sₐ (k := k) h = HopfAlgebra.antipode k h := rfl

theorem conv_apply (x y : H →ₐ[k] k) (h : H) :
    (WithConv.toConv x * WithConv.toConv y).ofConv h =
      LinearMap.mul' k k
        (TensorProduct.map x.toLinearMap y.toLinearMap (Coalgebra.comul (R := k) h)) := by
  rw [AlgHom.convMul_apply]
  induction (Coalgebra.comul (R := k) h) using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [Algebra.TensorProduct.lift_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
      AlgHom.toLinearMap_apply]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem comp_T (x g : H →ₐ[k] k) (h : H) :
    x (T g h) = (WithConv.toConv g * WithConv.toConv x).ofConv h := by
  rw [conv_apply, T_apply]
  induction (Coalgebra.comul (R := k) h) using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, AlgHom.toLinearMap_apply, map_smul,
      TensorProduct.map_tmul, LinearMap.mul'_apply, smul_eq_mul]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem convMul_compS_left (x : H →ₐ[k] k) :
    WithConv.toConv (x.comp Sₐ) * WithConv.toConv x = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  rw [conv_apply, AlgHom.convOne_apply]
  have key : ∀ z : H ⊗[k] H,
      LinearMap.mul' k k (TensorProduct.map (x.comp Sₐ).toLinearMap x.toLinearMap z) =
      x (LinearMap.mul' k H (LinearMap.rTensor H (HopfAlgebra.antipode k) z)) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [TensorProduct.map_tmul, LinearMap.mul'_apply,
        AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        Sₐ_apply, LinearMap.rTensor_tmul, map_mul]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [key, HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]

theorem convMul_compS_right (x : H →ₐ[k] k) :
    WithConv.toConv x * WithConv.toConv (x.comp Sₐ) = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  rw [conv_apply, AlgHom.convOne_apply]
  have key : ∀ z : H ⊗[k] H,
      LinearMap.mul' k k (TensorProduct.map x.toLinearMap (x.comp Sₐ).toLinearMap z) =
      x (LinearMap.mul' k H (LinearMap.lTensor H (HopfAlgebra.antipode k) z)) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [TensorProduct.map_tmul, LinearMap.mul'_apply,
        AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        Sₐ_apply, LinearMap.lTensor_tmul, map_mul]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [key, HopfAlgebra.mul_antipode_lTensor_comul_apply, AlgHom.commutes]

theorem exists_comp_T_eq (x y : H →ₐ[k] k) : ∃ g : H →ₐ[k] k, ∀ h, y h = x (T g h) := by
  refine ⟨(WithConv.toConv y * WithConv.toConv (x.comp Sₐ)).ofConv, fun h => ?_⟩
  rw [comp_T, WithConv.toConv_ofConv, mul_assoc, convMul_compS_left,
    mul_one, WithConv.ofConv_toConv]

theorem comul_lid_rTensor (b : H →ₐ[k] k) (z : H ⊗[k] H) :
    Coalgebra.comul (R := k) (TensorProduct.lid k H (LinearMap.rTensor H b.toLinearMap z)) =
      TensorProduct.lid k (H ⊗[k] H) (LinearMap.rTensor (H ⊗[k] H) b.toLinearMap
        (LinearMap.lTensor H (Coalgebra.comul (R := k)) z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul c h =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, AlgHom.toLinearMap_apply, map_smul,
      LinearMap.lTensor_tmul]
  | add a c ha hc => simp only [map_add, ha, hc]

theorem threefold (a b : H →ₐ[k] k) (w : (H ⊗[k] H) ⊗[k] H) :
    TensorProduct.lid k H (LinearMap.rTensor H a.toLinearMap
      (TensorProduct.lid k (H ⊗[k] H) (LinearMap.rTensor (H ⊗[k] H) b.toLinearMap
        (TensorProduct.assoc k H H H w)))) =
    TensorProduct.lid k H (LinearMap.rTensor H
      (LinearMap.mul' k k ∘ₗ TensorProduct.map b.toLinearMap a.toLinearMap) w) := by
  induction w using TensorProduct.inductionOn with
  | tmul z c =>
    induction z using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [TensorProduct.assoc_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
        AlgHom.toLinearMap_apply, map_smul, LinearMap.comp_apply, TensorProduct.map_tmul,
        LinearMap.mul'_apply, smul_smul, mul_comm (b u) (a v)]
    | add z₁ z₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
  | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]

theorem rTensor_conv (a b : H →ₐ[k] k) (w : H ⊗[k] H) :
    LinearMap.rTensor H (WithConv.toConv b * WithConv.toConv a).ofConv.toLinearMap w =
      LinearMap.rTensor H (LinearMap.mul' k k ∘ₗ TensorProduct.map b.toLinearMap a.toLinearMap)
        (LinearMap.rTensor H (Coalgebra.comul (R := k)) w) := by
  induction w using TensorProduct.inductionOn with
  | tmul c h =>
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, conv_apply, LinearMap.comp_apply]
  | add a c ha hc => simp only [map_add, ha, hc]

theorem T_T (a b : H →ₐ[k] k) (h : H) :
    T a (T b h) = T (WithConv.toConv b * WithConv.toConv a).ofConv h := by
  rw [T_apply, T_apply, T_apply, comul_lid_rTensor,
    ← Coalgebra.coassoc_apply, threefold, rTensor_conv]

theorem T_one (h : H) : T (1 : WithConv (H →ₐ[k] k)).ofConv h = h := by
  rw [T_apply]
  have : LinearMap.rTensor H (WithConv.ofConv (1 : WithConv (H →ₐ[k] k))).toLinearMap
      (Coalgebra.comul (R := k) h) =
      LinearMap.rTensor H (Coalgebra.counit (R := k) (A := H)) (Coalgebra.comul (R := k) h) := by
    induction (Coalgebra.comul (R := k) h) using TensorProduct.inductionOn with
    | tmul c x =>
      simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
        AlgHom.convOne_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
    | add a c ha hc => simp only [map_add, ha, hc]
  rw [this, Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]

theorem T_bijective (g : H →ₐ[k] k) : Function.Bijective (T g) := by
  have h1 : ∀ h, T (g.comp Sₐ) (T g h) = h := fun h => by
    rw [T_T, convMul_compS_right, T_one]
  have h2 : ∀ h, T g (T (g.comp Sₐ) h) = h := fun h => by
    rw [T_T, convMul_compS_left, T_one]
  exact ⟨fun a b hab => by rw [← h1 a, ← h1 b, hab], fun b => ⟨T (g.comp Sₐ) b, h2 b⟩⟩

theorem T_mem (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (g : H →ₐ[k] k) (x : H) (hx : x ∈ K) : T g x ∈ K := by
  rw [T_apply]
  have hsub : ∀ z ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b},
      TensorProduct.lid k H (LinearMap.rTensor H g.toLinearMap z) ∈ K := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨a, ha, b, hb, rfl⟩ := ht
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, AlgHom.toLinearMap_apply]
      exact K.smul_mem hb _
    | zero => simp only [map_zero]; exact K.zero_mem
    | add a b _ _ ha hb => simp only [map_add]; exact K.add_mem ha hb
    | smul c a _ ha => simp only [map_smul]; exact K.smul_mem ha c
  exact hsub _ (hΔ x hx)

end S17Tc1

open S17Tc1 in
theorem _root_.HopfAlgebra.bijective_translate_and_map_mem_and_exists_comp_translate_eq
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (τ : (H →ₐ[k] k) → (H →ₐ[k] H))
    (hτ : ∀ (g : H →ₐ[k] k) (h : H),
      τ g h = Algebra.TensorProduct.lid k H
        (Algebra.TensorProduct.map g (AlgHom.id k H) (Coalgebra.comul h))) :
    (∀ g, Function.Bijective (τ g)) ∧
    (∀ (K : Subalgebra k H),
      (∀ x ∈ K, Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) →
      ∀ g, ∀ x ∈ K, τ g x ∈ K) ∧
    (∀ x y : H →ₐ[k] k, ∃ g : H →ₐ[k] k, y = x.comp (τ g)) := by
  have hT : ∀ g h, τ g h = T g h := fun g h => by rw [hτ, lid_map_eq, T_apply]
  have hTf : ∀ g, (τ g : H → H) = T g := fun g => funext (hT g)
  refine ⟨fun g => ?_, fun K hΔ g x hx => ?_, fun x y => ?_⟩
  · rw [hTf]; exact T_bijective g
  · rw [hT]; exact T_mem K hΔ g x hx
  · obtain ⟨g, hg⟩ := exists_comp_T_eq x y
    exact ⟨g, AlgHom.ext fun h => by rw [AlgHom.comp_apply, hT]; exact hg h⟩

end AbelianVarieties.NOSProofs.HopfTranslation
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.HopfAugmentationIdeal

open _root_.Bialgebra
open _root_.Coalgebra
open _root_.TensorProduct
open _root_.Bialgebra.TensorProduct
open _root_.Coalgebra.TensorProduct

noncomputable section

namespace HopfRightTranslate

universe u v

variable (K : Type u) [Field K] (A : Type v) [CommRing A] [HopfAlgebra K A]

/-- Right translation by a rational point, expressed through comultiplication. -/
def rightTranslate (χ : A →ₐ[K] K) : A →ₐ[K] A :=
  (Algebra.TensorProduct.rid K K A).toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id K A) χ).comp (comulAlgHom K A))

/-- The canonical antipode used by right translation. -/
def antipodeAlgHom : A →ₐ[K] A := HopfAlgebra.antipodeAlgHom K A

variable {K A}

theorem antipodeAlgHom_apply (a : A) : antipodeAlgHom K A a = HopfAlgebra.antipode K a := rfl

theorem rightTranslate_apply_repr (χ : A →ₐ[K] K) (a : A) {ιrepr : Type*}
    (repr : Coalgebra.Repr K a ιrepr) :
    rightTranslate K A χ a = ∑ i ∈ repr.index, χ (repr.right i) • repr.left i := by
  change (Algebra.TensorProduct.rid K K A)
      (Algebra.TensorProduct.map (AlgHom.id K A) χ (comulAlgHom K A a)) = _
  have hcomul : comulAlgHom K A a = Coalgebra.comul (R := K) a := rfl
  rw [hcomul, ← repr.eq, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.rid_tmul]

theorem sum_counit_right_smul {a : A} {ιrepr : Type*} (repr : Coalgebra.Repr K a ιrepr) :
    ∑ i ∈ repr.index, Coalgebra.counit (R := K) (repr.right i) • repr.left i = a := by
  have h := Coalgebra.sum_tmul_counit_eq (R := K) repr
  have h2 := congrArg (TensorProduct.rid K A) h
  simp only [map_sum, TensorProduct.rid_tmul, one_smul] at h2
  exact h2

theorem counitAlgHom_comp_rightTranslate (χ : A →ₐ[K] K) :
    (counitAlgHom K A).comp (rightTranslate K A χ) = χ := by
  ext x
  change (counitAlgHom K A) ((Algebra.TensorProduct.rid K K A)
      (Algebra.TensorProduct.map (AlgHom.id K A) χ (comulAlgHom K A x))) = χ x
  have hcomul : comulAlgHom K A x = Coalgebra.comul (R := K) x := rfl
  rw [hcomul]
  have hmap : ((counitAlgHom K A).toLinearMap.comp
        (Algebra.TensorProduct.rid K K A).toLinearMap).comp
          (Algebra.TensorProduct.map (AlgHom.id K A) χ).toLinearMap
      = (TensorProduct.lid K K).toLinearMap.comp
          (χ.toLinearMap.lTensor K |>.comp ((Coalgebra.counit (R := K)).rTensor A)) := by
    refine TensorProduct.ext' fun a b => ?_
    change Coalgebra.counit (R := K) (χ b • a) = Coalgebra.counit (R := K) a * χ b
    rw [map_smul, smul_eq_mul, mul_comm]
  have h2 := congrArg (· (Coalgebra.comul (R := K) x)) (congrArg DFunLike.coe hmap)
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply,
    LinearEquiv.coe_toLinearMap, Coalgebra.rTensor_counit_comul, LinearMap.lTensor_tmul,
    TensorProduct.lid_tmul, one_smul] at h2
  exact h2

theorem rightTranslate_leftInverse (χ : A →ₐ[K] K) :
    Function.LeftInverse (rightTranslate K A (χ.comp (antipodeAlgHom K A)))
      (rightTranslate K A χ) := by
  intro a
  set ψ : A →ₐ[K] K := χ.comp (antipodeAlgHom K A)
  set R0 := ℛ K a
  rw [rightTranslate_apply_repr χ a R0, map_sum]
  simp_rw [map_smul]
  have hinner : ∀ i, rightTranslate K A ψ (R0.left i) =
      ∑ j ∈ (ℛ K (R0.left i)).index,
        ψ ((ℛ K (R0.left i)).right j) • (ℛ K (R0.left i)).left j :=
    fun i => rightTranslate_apply_repr ψ (R0.left i) (ℛ K (R0.left i))
  simp_rw [hinner, Finset.smul_sum, smul_smul]
  set a₁ : ∀ i, Coalgebra.Repr K (R0.left i) (A × A) := fun i => ℛ K (R0.left i)
  set a₂ : ∀ i, Coalgebra.Repr K (R0.right i) (A × A) := fun i => ℛ K (R0.right i)
  have hcoassoc := Coalgebra.sum_tmul_tmul_eq (R := K) R0 a₁ a₂
  let g : A ⊗[K] A →ₗ[K] K :=
    TensorProduct.lift (((LinearMap.mul K K).comp ψ.toLinearMap).compl₂ χ.toLinearMap)
  let φ : A ⊗[K] (A ⊗[K] A) →ₗ[K] A :=
    TensorProduct.lift ((LinearMap.flip (LinearMap.lsmul K A)).compl₂ g)
  have hφ : ∀ (x y z : A), φ (x ⊗ₜ (y ⊗ₜ z)) = (ψ y * χ z) • x := by
    intro x y z
    simp only [φ, g, TensorProduct.lift.tmul, LinearMap.compl₂_apply, LinearMap.flip_apply,
      LinearMap.lsmul_apply, LinearMap.comp_apply, LinearMap.mul_apply', AlgHom.toLinearMap_apply]
  have hcoassoc' := congrArg φ hcoassoc
  simp only [map_sum, hφ] at hcoassoc'
  calc ∑ i ∈ R0.index, ∑ j ∈ (a₁ i).index,
          (χ (R0.right i) * ψ ((a₁ i).right j)) • (a₁ i).left j
      = ∑ i ∈ R0.index, ∑ j ∈ (a₁ i).index,
          (ψ ((a₁ i).right j) * χ (R0.right i)) • (a₁ i).left j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm]
    _ = ∑ i ∈ R0.index, ∑ j ∈ (a₂ i).index,
          (ψ ((a₂ i).left j) * χ ((a₂ i).right j)) • R0.left i := hcoassoc'
    _ = ∑ i ∈ R0.index,
          (∑ j ∈ (a₂ i).index, ψ ((a₂ i).left j) * χ ((a₂ i).right j)) • R0.left i := by
        simp_rw [Finset.sum_smul]
    _ = ∑ i ∈ R0.index, (counit (R := K) (R0.right i)) • R0.left i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        simp_rw [ψ, AlgHom.comp_apply, antipodeAlgHom_apply, ← map_mul, ← map_sum]
        rw [HopfAlgebra.sum_antipode_mul_eq_smul (a₂ i), map_smul, map_one, smul_eq_mul,
          mul_one]
    _ = a := sum_counit_right_smul R0

theorem rightTranslate_rightInverse (χ : A →ₐ[K] K) :
    Function.RightInverse (rightTranslate K A (χ.comp (antipodeAlgHom K A)))
      (rightTranslate K A χ) := by
  intro a
  set ψ : A →ₐ[K] K := χ.comp (antipodeAlgHom K A)
  set R0 := ℛ K a
  rw [rightTranslate_apply_repr ψ a R0, map_sum]
  simp_rw [map_smul]
  have hinner : ∀ i, rightTranslate K A χ (R0.left i) =
      ∑ j ∈ (ℛ K (R0.left i)).index,
        χ ((ℛ K (R0.left i)).right j) • (ℛ K (R0.left i)).left j :=
    fun i => rightTranslate_apply_repr χ (R0.left i) (ℛ K (R0.left i))
  simp_rw [hinner, Finset.smul_sum, smul_smul]
  set a₁ : ∀ i, Coalgebra.Repr K (R0.left i) (A × A) := fun i => ℛ K (R0.left i)
  set a₂ : ∀ i, Coalgebra.Repr K (R0.right i) (A × A) := fun i => ℛ K (R0.right i)
  have hcoassoc := Coalgebra.sum_tmul_tmul_eq (R := K) R0 a₁ a₂
  let g : A ⊗[K] A →ₗ[K] K :=
    TensorProduct.lift (((LinearMap.mul K K).comp χ.toLinearMap).compl₂ ψ.toLinearMap)
  let φ : A ⊗[K] (A ⊗[K] A) →ₗ[K] A :=
    TensorProduct.lift ((LinearMap.flip (LinearMap.lsmul K A)).compl₂ g)
  have hφ : ∀ (x y z : A), φ (x ⊗ₜ (y ⊗ₜ z)) = (χ y * ψ z) • x := by
    intro x y z
    simp only [φ, g, TensorProduct.lift.tmul, LinearMap.compl₂_apply, LinearMap.flip_apply,
      LinearMap.lsmul_apply, LinearMap.comp_apply, LinearMap.mul_apply', AlgHom.toLinearMap_apply]
  have hcoassoc' := congrArg φ hcoassoc
  simp only [map_sum, hφ] at hcoassoc'
  calc ∑ i ∈ R0.index, ∑ j ∈ (a₁ i).index,
          (ψ (R0.right i) * χ ((a₁ i).right j)) • (a₁ i).left j
      = ∑ i ∈ R0.index, ∑ j ∈ (a₁ i).index,
          (χ ((a₁ i).right j) * ψ (R0.right i)) • (a₁ i).left j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm]
    _ = ∑ i ∈ R0.index, ∑ j ∈ (a₂ i).index,
          (χ ((a₂ i).left j) * ψ ((a₂ i).right j)) • R0.left i := hcoassoc'
    _ = ∑ i ∈ R0.index,
          (∑ j ∈ (a₂ i).index, χ ((a₂ i).left j) * ψ ((a₂ i).right j)) • R0.left i := by
        simp_rw [Finset.sum_smul]
    _ = ∑ i ∈ R0.index, (counit (R := K) (R0.right i)) • R0.left i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        simp_rw [ψ, AlgHom.comp_apply, antipodeAlgHom_apply, ← map_mul, ← map_sum]
        rw [HopfAlgebra.sum_mul_antipode_eq_smul (a₂ i), map_smul, map_one, smul_eq_mul,
          mul_one]
    _ = a := sum_counit_right_smul R0

/-- Right translation and its inverse defined by the antipode. -/
def rightTranslateEquiv (χ : A →ₐ[K] K) : A ≃ₐ[K] A :=
  AlgEquiv.ofAlgHom (rightTranslate K A χ)
    (rightTranslate K A (χ.comp (antipodeAlgHom K A)))
    (AlgHom.ext (rightTranslate_rightInverse χ))
    (AlgHom.ext (rightTranslate_leftInverse χ))

theorem rightTranslateEquiv_apply (χ : A →ₐ[K] K) (a : A) :
    rightTranslateEquiv χ a = rightTranslate K A χ a := rfl

theorem comap_ker_counitAlgHom_rightTranslate (χ : A →ₐ[K] K) :
    (RingHom.ker (counitAlgHom K A).toRingHom).comap (rightTranslate K A χ).toRingHom
      = RingHom.ker χ.toRingHom := by
  ext a
  simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  have := DFunLike.congr_fun (counitAlgHom_comp_rightTranslate χ) a
  simp only [AlgHom.comp_apply] at this
  rw [this]

end HopfRightTranslate

end

theorem _root_.HopfAlgebra.exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom
    (K : Type*) [Field K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] (χ : A →ₐ[K] K) :
    ∃ e : A ≃ₐ[K] A,
      (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom).comap e.toRingEquiv.toRingHom
        = RingHom.ker χ.toRingHom := by
  refine ⟨HopfRightTranslate.rightTranslateEquiv χ, ?_⟩
  change (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom).comap
      (HopfRightTranslate.rightTranslate K A χ).toRingHom = RingHom.ker χ.toRingHom
  exact HopfRightTranslate.comap_ker_counitAlgHom_rightTranslate χ

end AbelianVarieties.NOSProofs.HopfAugmentationIdeal
end
