/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Hopf ideals, quotient Hopf algebras and the tensor product torsor isomorphism
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace HopfIdealQuotients
universe u v

open scoped TensorProduct

theorem _root_.HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal
    {F : Type u} [Field F] {A : Type v} [CommRing A] [HopfAlgebra F A] (I : Ideal A)
    (hcomul : ∀ a ∈ I, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ F I)
      (Coalgebra.comul (R := F) a) = 0)
    (hcounit : ∀ a ∈ I, Coalgebra.counit (R := F) a = 0)
    (hanti : ∀ a ∈ I, HopfAlgebraStruct.antipode (R := F) a ∈ I) :
    ∃ (A' : Type v) (_ : CommRing A') (_ : HopfAlgebra F A') (π : A →ₐc[F] A'),
      Function.Surjective π ∧
      RingHom.ker (π : A →+* A') = I ∧
      (Coalgebra.IsCocomm F A → Coalgebra.IsCocomm F A') ∧
      (Module.Finite F A → Module.Finite F A') ∧
      (∀ (T : Type v) [CommRing T] [Algebra F T] (φ : A →ₐ[F] T),
        I ≤ RingHom.ker (φ : A →+* T) → ∃! φ' : A' →ₐ[F] T, φ'.comp (π : A →ₐ[F] A') = φ) := by
  have : I.IsHopfIdeal F :=
    { counit_eq_zero := fun {x} hx => hcounit x hx
      map_mkQ_comul_eq_zero := fun {x} hx => hcomul x hx
      antipode_mem := fun {x} hx => hanti x hx }
  let hH : HopfAlgebra F (A ⧸ I) := inferInstance
  let π : A →ₐc[F] (A ⧸ I) := Bialgebra.Quotient.mkBialgHom (R := F) I
  have hπ : ∀ a : A, π a = Ideal.Quotient.mk I a := fun a => rfl
  have hπalg : (π : A →ₐ[F] (A ⧸ I)) = Ideal.Quotient.mkₐ F I := by ext a; rfl
  refine ⟨A ⧸ I, inferInstance, hH, π, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x; exact ⟨a, hπ a⟩
  · ext a
    rw [RingHom.mem_ker]
    change π a = 0 ↔ a ∈ I
    rw [hπ, Ideal.Quotient.eq_zero_iff_mem]
  · intro hco
    refine ⟨?_⟩
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change TensorProduct.comm F (A ⧸ I) (A ⧸ I)
      (Coalgebra.comul (R := F) (Ideal.Quotient.mk I a)) =
        Coalgebra.comul (R := F) (Ideal.Quotient.mk I a)
    rw [Bialgebra.Quotient.comul_mk, ← TensorProduct.map_comm, Coalgebra.comm_comul]
  · intro hfin
    exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ F I).toLinearMap
        (Ideal.Quotient.mkₐ_surjective F I)
  · intro T _ _ φ hφ
    refine ⟨Ideal.Quotient.liftₐ I φ (fun a ha => hφ ha), ?_, ?_⟩
    · rw [hπalg]; ext a; rfl
    · intro ψ hψ
      apply Ideal.Quotient.algHom_ext
      rw [← hπalg, hψ]
      ext a; rfl

end HopfIdealQuotients
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_exists_algEquiv_subalgebraTensor_tensorQuotient_of_comul_mem_span.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace SubalgebraTensorQuotients
open scoped TensorProduct

universe u v

namespace TensorTorsor

variable {k : Type u} [CommRing k] {H : Type v} [CommRing H] [HopfAlgebra k H]
variable (K : Subalgebra k H)

/-- The ideal generated by the augmentation ideal of the subalgebra. -/
def J : Ideal H := Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0}

/-- The quotient by the ideal generated by the subalgebra augmentation ideal. -/
abbrev Q : Type v := H ⧸ J K

/-- The quotient algebra map. -/
def π : H →ₐ[k] Q K := Ideal.Quotient.mkₐ k (J K)

theorem π_eq_algebraMap_counit_of_mem {x : H} (hx : x ∈ K) :
    π K x = algebraMap k (Q K) (Coalgebra.counit (R := k) x) := by
  have hmem : x - algebraMap k H (Coalgebra.counit (R := k) x) ∈ J K := by
    apply Ideal.subset_span
    refine ⟨K.sub_mem hx (K.algebraMap_mem _), ?_⟩
    rw [map_sub, Bialgebra.counit_algebraMap, sub_self]
  have h0 : π K (x - algebraMap k H (Coalgebra.counit (R := k) x)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h0
  exact h0

/-- The canonical map from the tensor product over k to the tensor product over K. -/
noncomputable def mapKₐ : H ⊗[k] H →ₐ[k] H ⊗[↥K] H :=
  Algebra.TensorProduct.mapOfCompatibleSMul ↥K k k H H

/-- The underlying linear map of the canonical change of tensor coefficient ring. -/
noncomputable def mapK : H ⊗[k] H →ₗ[k] H ⊗[↥K] H := (mapKₐ K).toLinearMap

@[scoped simp] theorem mapK_tmul (x y : H) :
    mapK K (x ⊗ₜ[k] y) = x ⊗ₜ[↥K] y := rfl

/-- The inverse torsor map before passing to the quotient. -/
noncomputable def ψ₀ : H →ₐ[k] H ⊗[↥K] H :=
  (mapKₐ K).comp ((Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom k H) (AlgHom.id k H)).comp
      (Bialgebra.comulAlgHom k H))

theorem ψ₀_apply (c : H) :
    ψ₀ K c = mapK K ((HopfAlgebra.antipode k).rTensor H (Coalgebra.comul (R := k) c)) := by
  simp only [ψ₀, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  change mapK K (Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom k H) (AlgHom.id k H)
      (Coalgebra.comul c)) = _
  congr 1

theorem ψ₀_eq_zero_of_mem {a : H} (ha : a ∈ K) (hε : Coalgebra.counit (R := k) a = 0)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) :
    ψ₀ K a = 0 := by
  have key : ∀ t ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b},
      mapK K ((HopfAlgebra.antipode k).rTensor H t)
        = (LinearMap.mul' k H ((HopfAlgebra.antipode k).rTensor H t)) ⊗ₜ[↥K] (1 : H) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨x, _, y, hy, rfl⟩ := ht
      simp only [LinearMap.rTensor_tmul, mapK_tmul, LinearMap.mul'_apply]
      rw [show (HopfAlgebra.antipode k x) ⊗ₜ[↥K] y = (HopfAlgebra.antipode k x) ⊗ₜ[↥K] ((⟨y, hy⟩ :
          ↥K) • (1 : H)) by
        rw [Subalgebra.smul_def, smul_eq_mul, mul_one]]
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Subalgebra.smul_def, smul_eq_mul,
          mul_comm]
    | zero => simp only [map_zero, TensorProduct.zero_tmul]
    | add s t _ _ hs ht => simp only [map_add, TensorProduct.add_tmul, hs, ht]
    | smul c t _ ht => simp only [map_smul, ht, TensorProduct.smul_tmul']
  rw [ψ₀_apply, key _ (hΔ a ha), HopfAlgebra.mul_antipode_rTensor_comul_apply, hε, map_zero,
    TensorProduct.zero_tmul]

variable (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
  Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})

/-- The base change of the quotient algebra to the original Hopf algebra. -/
abbrev C : Type v := H ⊗[k] Q K

/-- The quotient map on the second tensor factor. -/
noncomputable def θ : H ⊗[k] H →ₐ[k] C K := Algebra.TensorProduct.map (AlgHom.id k H) (π K)

@[scoped simp] theorem θ_tmul (x y : H) : θ K (x ⊗ₜ[k] y) = x ⊗ₜ[k] π K y := rfl

theorem θ_eq_of_mem_span (t : H ⊗[k] H)
    (ht : t ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) :
    θ K t = (TensorProduct.rid k H ((Coalgebra.counit (R := k) (A := H)).lTensor H t)) ⊗ₜ[k] (1 : Q
        K) := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨x, _, y, hy, rfl⟩ := ht
    simp only [θ_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    rw [π_eq_algebraMap_counit_of_mem K hy, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  | zero => simp only [map_zero, TensorProduct.zero_tmul]
  | add s t _ _ hs ht => simp only [map_add, TensorProduct.add_tmul, hs, ht]
  | smul c t _ ht => simp only [map_smul, ht, TensorProduct.smul_tmul']

include hΔ in
theorem θ_comul_of_mem {a : H} (ha : a ∈ K) : θ K (Coalgebra.comul (R := k) a) = a ⊗ₜ[k] (1 : Q K)
    := by
  rw [θ_eq_of_mem_span K _ (hΔ a ha), Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul,
      one_smul]

/-- Comultiplication followed by the quotient on the second factor. -/
noncomputable def g : H →ₐ[↥K] C K :=
  { ((θ K).comp (Bialgebra.comulAlgHom k H)).toRingHom with
    commutes' := fun a => by
      change θ K (Coalgebra.comul (R := k) (a : H)) = algebraMap (↥K) (C K) a
      rw [θ_comul_of_mem K hΔ a.2]
      rfl }

theorem g_apply (h : H) : g K hΔ h = θ K (Coalgebra.comul (R := k) h) := rfl

/-- The canonical torsor map over the subalgebra. -/
noncomputable def β : H ⊗[↥K] H →ₐ[H] C K :=
  Algebra.TensorProduct.lift (Algebra.ofId H (C K)) (g K hΔ) (fun _ _ => Commute.all _ _)

theorem β_tmul (x y : H) : β K hΔ (x ⊗ₜ[↥K] y) = (x ⊗ₜ[k] (1 : Q K)) * θ K (Coalgebra.comul (R :=
    k) y) := by
  rw [β, Algebra.TensorProduct.lift_tmul]
  rfl

/-- The inverse torsor map on the quotient algebra. -/
noncomputable def ψ : Q K →ₐ[k] H ⊗[↥K] H :=
  Ideal.Quotient.liftₐ (J K) (ψ₀ K) (fun a ha => by
    have hle : J K ≤ RingHom.ker (ψ₀ K).toRingHom := by
      rw [J, Ideal.span_le]
      rintro x ⟨hxK, hxε⟩
      exact ψ₀_eq_zero_of_mem K hxK hxε hΔ
    exact hle ha)

theorem ψ_π (c : H) : ψ K hΔ (π K c) = ψ₀ K c := rfl

/-- The inverse torsor map after scalar extension. -/
noncomputable def δ : C K →ₐ[H] H ⊗[↥K] H :=
  Algebra.TensorProduct.lift (Algebra.ofId H (H ⊗[↥K] H)) (ψ K hΔ) (fun _ _ => Commute.all _ _)

theorem δ_tmul (x c : H) : δ K hΔ (x ⊗ₜ[k] π K c) = x • ψ₀ K c := by
  rw [δ, Algebra.TensorProduct.lift_tmul, ψ_π, Algebra.ofId_apply]
  exact (Algebra.smul_def x (ψ₀ K c)).symm

omit [HopfAlgebra k H] in
theorem assoc_symm_lTensor_rTensor_assoc [Module k H] (f : H →ₗ[k] H) :
    (TensorProduct.assoc k H H H).symm.toLinearMap ∘ₗ (f.rTensor H).lTensor H ∘ₗ
      (TensorProduct.assoc k H H H).toLinearMap = (f.lTensor H).rTensor H := by
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

theorem smul_mapK (x : H) (s : H ⊗[k] H) :
    x • mapK K s = mapK K ((LinearMap.mul' k H).rTensor H ((TensorProduct.assoc k H H H).symm (x
        ⊗ₜ[k] s))) := by
  induction s using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [mapK_tmul, TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul,
        LinearMap.mul'_apply]
    rw [TensorProduct.smul_tmul', smul_eq_mul]
  | add s t hs ht => simp only [map_add, smul_add, hs, ht, TensorProduct.tmul_add]

theorem δ_θ (t : H ⊗[k] H) :
    δ K hΔ (θ K t) = mapK K ((LinearMap.mul' k H).rTensor H ((TensorProduct.assoc k H H H).symm
      ((((HopfAlgebra.antipode k).rTensor H) ∘ₗ Coalgebra.comul).lTensor H t))) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [θ_tmul, δ_tmul, ψ₀_apply, smul_mapK]
    rfl
  | add s t hs ht => simp only [map_add, hs, ht]

theorem sweedler₁ (h : H) :
    (LinearMap.mul' k H).rTensor H ((TensorProduct.assoc k H H H).symm
      ((((HopfAlgebra.antipode k).rTensor H) ∘ₗ Coalgebra.comul).lTensor H (Coalgebra.comul (R :=
          k) h)))
      = (1 : H) ⊗ₜ[k] h := by
  rw [LinearMap.lTensor_comp, LinearMap.comp_apply, ← Coalgebra.coassoc_apply]
  have h1 := LinearMap.congr_fun (assoc_symm_lTensor_rTensor_assoc (k := k) (H := H)
      (HopfAlgebra.antipode k))
    ((Coalgebra.comul (R := k)).rTensor H (Coalgebra.comul (R := k) h))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at h1
  rw [h1, ← LinearMap.comp_apply (f := (LinearMap.mul' k H).rTensor H), ← LinearMap.rTensor_comp,
    ← LinearMap.comp_apply (f := ((LinearMap.mul' k H) ∘ₗ (HopfAlgebra.antipode k).lTensor
        H).rTensor H),
    ← LinearMap.rTensor_comp, LinearMap.comp_assoc, HopfAlgebra.mul_antipode_lTensor_comul,
    LinearMap.rTensor_comp, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul]
  simp only [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]

theorem δ_β_includeRight (h : H) : δ K hΔ (β K hΔ ((1 : H) ⊗ₜ[↥K] h)) = (1 : H) ⊗ₜ[↥K] h := by
  rw [β_tmul, show ((1 : H) ⊗ₜ[k] (1 : Q K)) = 1 from rfl, one_mul, δ_θ, sweedler₁, mapK_tmul]

theorem sweedler₂ (c : H) :
    (LinearMap.mul' k H).rTensor H ((TensorProduct.assoc k H H H).symm
      ((Coalgebra.comul (R := k)).lTensor H (((HopfAlgebra.antipode k).rTensor H) (Coalgebra.comul
          (R := k) c))))
      = (1 : H) ⊗ₜ[k] c := by
  have e1 : (Coalgebra.comul (R := k)).lTensor H (((HopfAlgebra.antipode k).rTensor H)
      (Coalgebra.comul (R := k) c))
      = ((HopfAlgebra.antipode k).rTensor (H ⊗[k] H)) ((Coalgebra.comul (R := k)).lTensor H
          (Coalgebra.comul (R := k) c)) := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply (g := (Coalgebra.comul (R := k)).lTensor H),
      LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor]
  rw [e1, ← Coalgebra.coassoc_apply]
  have e2 : ∀ t : (H ⊗[k] H) ⊗[k] H, (TensorProduct.assoc k H H H).symm
      (((HopfAlgebra.antipode k).rTensor (H ⊗[k] H)) (TensorProduct.assoc k H H H t))
      = ((HopfAlgebra.antipode k).rTensor H).rTensor H t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul s z =>
      induction s using TensorProduct.inductionOn with
      | tmul x y => rfl
      | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [e2, ← LinearMap.comp_apply (f := (LinearMap.mul' k H).rTensor H), ← LinearMap.rTensor_comp,
    ← LinearMap.comp_apply (f := ((LinearMap.mul' k H) ∘ₗ (HopfAlgebra.antipode k).rTensor
        H).rTensor H),
    ← LinearMap.rTensor_comp, LinearMap.comp_assoc, HopfAlgebra.mul_antipode_rTensor_comul,
    LinearMap.rTensor_comp, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul]
  simp only [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]

theorem β_mapK (x y : H) : β K hΔ (mapK K (x ⊗ₜ[k] y)) = (x ⊗ₜ[k] (1 : Q K)) * θ K (Coalgebra.comul
    (R := k) y) := by
  rw [mapK_tmul, β_tmul]

theorem β_ψ₀ (c : H) : β K hΔ (ψ₀ K c) = (1 : H) ⊗ₜ[k] π K c := by
  rw [ψ₀_apply]
  have hgen : ∀ s : H ⊗[k] H, β K hΔ (mapK K s)
      = θ K ((LinearMap.mul' k H).rTensor H ((TensorProduct.assoc k H H H).symm
          ((Coalgebra.comul (R := k)).lTensor H s))) := by
    intro s
    induction s using TensorProduct.inductionOn with
    | tmul x y =>
      rw [β_mapK, LinearMap.lTensor_tmul]
      have : ∀ w : H ⊗[k] H, (x ⊗ₜ[k] (1 : Q K)) * θ K w
          = θ K ((LinearMap.mul' k H).rTensor H ((TensorProduct.assoc k H H H).symm (x ⊗ₜ[k] w)))
              := by
        intro w
        induction w using TensorProduct.inductionOn with
        | tmul a b =>
          rw [θ_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
            TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, LinearMap.mul'_apply, θ_tmul]
        | add a b ha hb => simp only [map_add, mul_add, ha, hb, TensorProduct.tmul_add]
      exact this _
    | add s t hs ht => simp only [map_add, hs, ht]
  rw [hgen, sweedler₂, θ_tmul]

theorem β_δ_includeRight (c : H) : β K hΔ (δ K hΔ ((1 : H) ⊗ₜ[k] π K c)) = (1 : H) ⊗ₜ[k] π K c := by
  rw [δ_tmul, one_smul, β_ψ₀]

theorem δ_comp_β : (δ K hΔ).comp (β K hΔ) = AlgHom.id H (H ⊗[↥K] H) := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply AlgHom.ext
    intro h
    change δ K hΔ (β K hΔ ((1 : H) ⊗ₜ[↥K] h)) = (1 : H) ⊗ₜ[↥K] h
    exact δ_β_includeRight K hΔ h

theorem β_comp_δ : (β K hΔ).comp (δ K hΔ) = AlgHom.id H (C K) := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro c
    change β K hΔ (δ K hΔ ((1 : H) ⊗ₜ[k] π K c)) = (1 : H) ⊗ₜ[k] π K c
    exact β_δ_includeRight K hΔ c

/-- The tensor product torsor isomorphism. -/
noncomputable def βEquiv : (H ⊗[↥K] H) ≃ₐ[H] C K :=
  AlgEquiv.ofAlgHom (β K hΔ) (δ K hΔ) (β_comp_δ K hΔ) (δ_comp_β K hΔ)

end TensorTorsor

theorem _root_.HopfAlgebra.exists_algEquiv_subalgebraTensor_tensorQuotient_of_comul_mem_span
    {k : Type u} [CommRing k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) :
    ∃ β : (H ⊗[↥K] H) ≃ₐ[H]
        (H ⊗[k] (H ⧸ Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0})),
      ∀ h₁ h₂ : H, β (h₁ ⊗ₜ[↥K] h₂) =
        (h₁ ⊗ₜ[k] (1 : H ⧸ Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0})) *
          Algebra.TensorProduct.map (AlgHom.id k H)
            (Ideal.Quotient.mkₐ k (Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0}))
            (Coalgebra.comul (R := k) h₂) :=
  ⟨TensorTorsor.βEquiv K hΔ, fun h₁ h₂ => TensorTorsor.β_tmul K hΔ h₁ h₂⟩

end SubalgebraTensorQuotients
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_exists_hopfAlgebra_surjective_ker_eq_span_of_comul_mem_span_of_antipode_mem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace HopfSubalgebraQuotients
open scoped TensorProduct

universe u v w

namespace AugmentationIdeal
variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]

/-- The product of the counits on the two tensor factors. -/
noncomputable def ee : H ⊗[k] H →ₗ[k] k :=
  (TensorProduct.lid k k).toLinearMap ∘ₗ
    TensorProduct.map (Coalgebra.counit (R := k) (A := H)) (Coalgebra.counit (R := k) (A := H))

theorem ee_tmul (a b : H) : ee (k := k) (a ⊗ₜ[k] b) = Coalgebra.counit (R := k) a *
    Coalgebra.counit (R := k) b := by
  rfl

theorem ee_comul (a : H) : ee (k := k) (Coalgebra.comul (R := k) a) = Coalgebra.counit (R := k) a
    := by
  have h1 : TensorProduct.map (Coalgebra.counit (R := k) (A := H)) (Coalgebra.counit (R := k) (A :=
      H))
      (Coalgebra.comul (R := k) a) = (1 : k) ⊗ₜ[k] Coalgebra.counit (R := k) a := by
    rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul,
      LinearMap.lTensor_tmul]
  change (TensorProduct.lid k k)
    (TensorProduct.map (Coalgebra.counit (R := k)) (Coalgebra.counit (R := k))
      (Coalgebra.comul (R := k) a)) = Coalgebra.counit (R := k) a
  rw [h1, TensorProduct.lid_tmul, one_smul]

theorem map_eq_of_mem_span (K' : Subalgebra k H) {B : Type w} [CommRing B] [Algebra k B] (φ : H
    →ₐ[k] B)
    (hφ : ∀ x ∈ K', φ x = algebraMap k B (Coalgebra.counit (R := k) x))
    {t : H ⊗[k] H} (ht : t ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b}) :
    Algebra.TensorProduct.map φ φ t = ee (k := k) t • (1 : B ⊗[k] B) := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      rw [Algebra.TensorProduct.map_tmul, hφ a ha, hφ b hb, ee_tmul, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
            TensorProduct.tmul_smul,
        smul_smul, mul_comm, Algebra.TensorProduct.one_def]
  | zero => simp only [map_zero, zero_smul]
  | add x y _ _ hx hy => rw [map_add, hx, hy, map_add, add_smul]
  | smul c x _ hx => rw [map_smul, hx, map_smul, smul_eq_mul, mul_smul]

end AugmentationIdeal

theorem
    _root_.HopfAlgebra.exists_hopfAlgebra_surjective_ker_eq_span_of_comul_mem_span_of_antipode_mem
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K' : Subalgebra k H)
    (hΔ' : ∀ x ∈ K', Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b})
    (hS' : ∀ x ∈ K', HopfAlgebra.antipode k x ∈ K') :
    ∃ (Hb : Type v) (_ : CommRing Hb) (_ : HopfAlgebra k Hb) (π : H →ₐc[k] Hb),
      Function.Surjective π ∧
      RingHom.ker (π : H →+* Hb) = Ideal.span {x : H | x ∈ K' ∧ Coalgebra.counit (R := k) x = 0} ∧
      (∀ x : H, Coalgebra.counit (R := k) (π x) = Coalgebra.counit (R := k) x) ∧
      (∀ x : H, π (HopfAlgebra.antipode k x) = HopfAlgebra.antipode k (π x)) ∧
      ∀ (K : Subalgebra k H),
        (∀ x ∈ K, Coalgebra.comul (R := k) x ∈
          Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) →
        (∀ x ∈ K, HopfAlgebra.antipode k x ∈ K) →
        (∀ y ∈ K.map (π : H →ₐ[k] Hb), Coalgebra.comul (R := k) y ∈
          Submodule.span k {t : Hb ⊗[k] Hb |
            ∃ a ∈ K.map (π : H →ₐ[k] Hb), ∃ b ∈ K.map (π : H →ₐ[k] Hb), t = a ⊗ₜ[k] b}) ∧
        (∀ y ∈ K.map (π : H →ₐ[k] Hb), HopfAlgebra.antipode k y ∈ K.map (π : H →ₐ[k] Hb)) := by
  classical
  set J : Ideal H := Ideal.span {x : H | x ∈ K' ∧ Coalgebra.counit (R := k) x = 0} with hJ
  let mk : H →ₐ[k] H ⧸ J := Ideal.Quotient.mkₐ k J
  have hmk : ∀ x ∈ K', mk x = algebraMap k (H ⧸ J) (Coalgebra.counit (R := k) x) := by
    intro x hx
    have hmem : x - algebraMap k H (Coalgebra.counit (R := k) x) ∈ J :=
      Ideal.subset_span ⟨K'.sub_mem hx (K'.algebraMap_mem _), by
        rw [map_sub, Bialgebra.counit_algebraMap, sub_self]⟩
    have h0 : mk (x - algebraMap k H (Coalgebra.counit (R := k) x)) = 0 := by
      change Ideal.Quotient.mkₐ k J _ = 0
      rw [Ideal.Quotient.mkₐ_eq_mk]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [map_sub, sub_eq_zero, AlgHom.commutes] at h0
    exact h0
  have hcomul : ∀ a ∈ J, Algebra.TensorProduct.map mk mk (Coalgebra.comul (R := k) a) = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨hxK, hxε⟩ := hx
        rw [AugmentationIdeal.map_eq_of_mem_span K' mk hmk (hΔ' x hxK), AugmentationIdeal.ee_comul,
            hxε, zero_smul]
    | zero => rw [map_zero, map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_eq_mul, Bialgebra.comul_mul, map_mul, hx, mul_zero]
  have hcounit : ∀ a ∈ J, Coalgebra.counit (R := k) a = 0 := by
    have hle : J ≤ RingHom.ker (Bialgebra.counitAlgHom k H) :=
      Ideal.span_le.mpr (fun x hx => by
        change x ∈ RingHom.ker (Bialgebra.counitAlgHom k H)
        rw [RingHom.mem_ker]; exact hx.2)
    intro a ha
    have := hle ha
    rwa [RingHom.mem_ker] at this
  have hanti : ∀ a ∈ J, HopfAlgebraStruct.antipode (R := k) a ∈ J := by
    have hmap : Ideal.map (HopfAlgebra.antipodeAlgHom k H) J ≤ J := by
      rw [Ideal.map_span]
      apply Ideal.span_mono
      rintro _ ⟨x, ⟨hxK, hxε⟩, rfl⟩
      exact ⟨hS' x hxK, by
        change Coalgebra.counit (R := k) (HopfAlgebra.antipode k x) = 0
        rw [HopfAlgebra.counit_antipode, hxε]⟩
    intro a ha
    exact hmap (Ideal.mem_map_of_mem (HopfAlgebra.antipodeAlgHom k H) ha)
  have : J.IsHopfIdeal k :=
    { counit_eq_zero := fun {x} hx => hcounit x hx
      map_mkQ_comul_eq_zero := fun {x} hx => hcomul x hx
      antipode_mem := fun {x} hx => hanti x hx }
  let Hb := H ⧸ J
  let π : H →ₐc[k] Hb := Bialgebra.Quotient.mkBialgHom (R := k) J
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (π : H →+* Hb) = J := by
    ext x
    exact Ideal.Quotient.eq_zero_iff_mem
  have hε : ∀ x : H, Coalgebra.counit (R := k) (π x) = Coalgebra.counit (R := k) x :=
    fun x => CoalgHomClass.counit_comp_apply π x
  have hSπ : ∀ x : H, π (HopfAlgebra.antipode k x) = HopfAlgebra.antipode k (π x) := by
    intro x
    exact (HopfAlgebra.Quotient.antipode_mk (R := k) J x).symm
  refine ⟨Hb, inferInstance, inferInstance, π, hπ, hker, hε, hSπ, ?_⟩
  intro K hΔ hS
  constructor
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.mp hy
    change Coalgebra.comul (R := k) (π x) ∈ _
    rw [← CoalgHomClass.map_comp_comul_apply π x]
    have aux : ∀ t : H ⊗[k] H, t ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k]
        b} →
        TensorProduct.map ((π : H →ₐ[k] Hb) : H →ₗ[k] Hb) ((π : H →ₐ[k] Hb) : H →ₗ[k] Hb) t ∈
          Submodule.span k {t : Hb ⊗[k] Hb |
            ∃ a ∈ K.map (π : H →ₐ[k] Hb), ∃ b ∈ K.map (π : H →ₐ[k] Hb), t = a ⊗ₜ[k] b} := by
      intro t ht
      induction ht using Submodule.span_induction with
      | mem t ht =>
          obtain ⟨a, ha, b, hb, rfl⟩ := ht
          rw [TensorProduct.map_tmul]
          exact Submodule.subset_span ⟨π a, Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩, π b,
            Subalgebra.mem_map.mpr ⟨b, hb, rfl⟩, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add s t _ _ hs ht => rw [map_add]; exact Submodule.add_mem _ hs ht
      | smul c t _ ht => rw [map_smul]; exact Submodule.smul_mem _ c ht
    exact aux _ (hΔ x hx)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.mp hy
    change HopfAlgebra.antipode k (π x) ∈ _
    rw [← hSπ]
    exact Subalgebra.mem_map.mpr ⟨_, hS x hx, rfl⟩

end HopfSubalgebraQuotients
end NOSProofs
end AbelianVarieties
end
