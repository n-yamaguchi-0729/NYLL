/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateCupConnecting
public import Nyll.GaloisCohomology.Cyclic.IntegralTateGroupTransferConnecting
public import Nyll.GaloisCohomology.Cyclic.IntegralTateTensorShift
public import Nyll.GaloisCohomology.GroupTheory.TensorShiftExactness

/-!
# Subgroup restriction of integral Tate cup products

The actual subgroup restriction preserves cup products in every integer
bidegree. Starting at degree zero on the right, the split connecting
identities propagate the law upwards and downwards.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped RepTensor

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    [Fintype H] [Fintype (G ⧸ H)]

omit [Fintype G] [Fintype (G ⧸ H)] in
/-- The subgroup restriction of a tensor with an original induced middle
term is Tate acyclic by the same coset-trace calculation. -/
theorem tate_resTensorIndBot_isZero [Finite G] (A : Rep.{u} ℤ G) (B : Rep.{u} ℤ (⊥ : Subgroup G))
    (n : ℤ) : IsZero (tate (Rep.res H.subtype (A ⊗ᵣ Rep.ind (⊥ : Subgroup G).subtype B)) n) := by
  classical
  let : Fintype (G ⧸ (⊥ : Subgroup G)) := Fintype.ofFinite _
  let A' := Rep.res H.subtype A
  let C := Rep.res H.subtype (Rep.coind (⊥ : Subgroup G).subtype B)
  let e := (Rep.resFunctor H.subtype).mapIso (Rep.indCoindIso.{u} B)
  let : Module ℤ C := C.hV2
  let proj := subgroupCoindTraceProjection H B
  let pr : C →ₗ[ℤ] C :=
    { toFun := proj
      map_add' := proj.map_add
      map_smul' := fun a x => by
        rw [RingHom.id_apply]
        exact (congrArg proj (int_smul_eq_zsmul C.hV2 a x)).trans
          ((proj.map_zsmul a x).trans (int_smul_eq_zsmul C.hV2 a (proj x)).symm) }
  exact (tate_tensor_isZero_of_trace_identity A' C pr
    (subgroupCoindTraceProjection_trace H B) n).of_iso
      ((tateFunctor H n).mapIso ((Rep.diagonalTensorLeft A').mapIso e))

private theorem restrictCup_sign (A : Rep.{u} ℤ G) (p n : ℤ) (x : tate A n) :
    tateRestrict H A n (p.negOnePow • x) = p.negOnePow • tateRestrict H A n x := by
  simp only [Units.smul_def]
  exact (tateRestrict H A n).toAddMonoidHom.map_zsmul (p.negOnePow : ℤ) x

private theorem negOnePow_smul_smul {V : Type*} [AddCommGroup V] [Module ℤ V]
    (p : ℤ) (x : V) : p.negOnePow • (p.negOnePow • x) = x := by
  calc
    _ = (p.negOnePow * p.negOnePow) • x := (mul_smul _ _ _).symm
    _ = (1 : ℤˣ) • x := congrArg (· • x) (Int.units_mul_self p.negOnePow)
    _ = x := one_smul _ _

private theorem restrictCup_step_up (A B : Rep.{u} ℤ G) {p q r : ℤ} (h : p + q = r)
    (x : tate A p) (y : tate B (q + 1))
    (ih : ∀ z : tate (Rep.coindShiftUp B) q,
      tateRestrict H (A ⊗ᵣ Rep.coindShiftUp B) r
          (tateCup A (Rep.coindShiftUp B) p q r h x z) =
        tateCup (Rep.res H.subtype A) (Rep.res H.subtype (Rep.coindShiftUp B)) p q r h
          (tateRestrict H A p x) (tateRestrict H (Rep.coindShiftUp B) q z)) :
    tateRestrict H (A ⊗ᵣ B) (r + 1) (tateCup A B p (q + 1) (r + 1) (by omega) x y) =
      tateCup (Rep.res H.subtype A) (Rep.res H.subtype B) p (q + 1) (r + 1) (by omega)
        (tateRestrict H A p x) (tateRestrict H B (q + 1) y) := by
  obtain ⟨z, rfl⟩ := (coindShiftUpEquiv B q).surjective y
  let A' := Rep.res H.subtype A
  let S := Rep.coindShiftSequence B
  let F : Rep.{u} ℤ G ⥤ Rep.{u} ℤ H := Rep.resFunctor H.subtype
  let hS := Rep.coindShiftSequence_shortExact B
  let s := Rep.coindShiftSequence_forget_splitting B
  let hT := Rep.tensorLeft_shortExact_of_forget_splitting A s
  let sT := Rep.tensorLeft_forget_splitting A s
  let hS' := subgroupRestrict_shortExact H hS
  let s' : ((S.map F).map (forget₂ (Rep.{u} ℤ H) (ModuleCat.{u} ℤ))).Splitting := s
  have hC := tateCup_connecting_right A hS s h x z
  change tateCup A B p (q + 1) (r + 1) (by omega) x (coindShiftUpEquiv B q z) =
    p.negOnePow • tateδ hT r (tateCup A (Rep.coindShiftUp B) p q r h x z) at hC
  have hy := tateRestrict_connecting H hS s q z
  change tateRestrict H B (q + 1) (coindShiftUpEquiv B q z) =
    tateδ hS' q (tateRestrict H (Rep.coindShiftUp B) q z) at hy
  let B₁ := Rep.coindShiftUp B
  let v := tateCup A B₁ p q r h x z
  let xx := tateRestrict H A p x
  let zz := tateRestrict H B₁ q z
  let v' := tateCup A' (Rep.res H.subtype B₁) p q r h xx zz
  let hT' := subgroupRestrict_shortExact H hT
  let f := tateCup A' (Rep.res H.subtype B) p (q + 1) (r + 1) (by omega) xx
  have hd := tateRestrict_connecting H hT sT r v
  have hc' := tateCup_connecting_right A' hS' s' h xx zz
  let X := tate (Rep.res H.subtype (A ⊗ᵣ B)) (r + 1)
  let sign (w : X) : X := p.negOnePow • w
  let res₁ := tateRestrict H (A ⊗ᵣ B) (r + 1)
  have h₁ := congrArg res₁ hC
  have h₂ := restrictCup_sign H (A ⊗ᵣ B) p (r + 1) (tateδ hT r v)
  have h₃ := congrArg sign hd
  have h₄ := congrArg (fun w => sign (tateδ hT' r w)) (ih z)
  have h₅ : sign (tateδ hT' r v') = f (tateδ hS' q zz) := hc'.symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (congrArg f hy.symm)))))

private theorem cupConnectingRight_signed_boundary
    {S : ShortComplex (Rep.{u} ℤ G)} (A : Rep.{u} ℤ G) (hS : S.ShortExact)
    (s : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting)
    {p q r : ℤ} (h : p + q = r) (x : tate A p) (y : tate S.X₃ q) :
    tateδ (Rep.tensorLeft_shortExact_of_forget_splitting A s) r (tateCup A S.X₃ p q r h x y) =
      p.negOnePow • tateCup A S.X₁ p (q + 1) (r + 1) (by omega) x (tateδ hS q y) := by
  let X := tate (A ⊗ᵣ S.X₁) (r + 1)
  let z : X := tateδ (Rep.tensorLeft_shortExact_of_forget_splitting A s) r
    (tateCup A S.X₃ p q r h x y)
  exact (negOnePow_smul_smul p z).symm.trans
    (congrArg (fun w : X => p.negOnePow • w) (tateCup_connecting_right A hS s h x y).symm)

private theorem restrictCup_down_left_boundary (A B : Rep.{u} ℤ G) {p q r : ℤ} (h : p + q = r)
    (x : tate A p) (y : tate B q) :
    let hS := Rep.indShiftSequence_shortExact B
    let s := Rep.indShiftSequence_forget_splitting B
    let hT := Rep.tensorLeft_shortExact_of_forget_splitting A s
    tateδ (subgroupRestrict_shortExact H hT) r
        (tateRestrict H (A ⊗ᵣ B) r (tateCup A B p q r h x y)) =
      p.negOnePow • tateRestrict H (A ⊗ᵣ Rep.indShiftDown B) (r + 1)
        (tateCup A (Rep.indShiftDown B) p (q + 1) (r + 1) (by omega) x (tateδ hS q y)) := by
  intro hS s hT
  let v := tateCup A B p q r h x y
  let B₁ := Rep.indShiftDown B
  let v' := tateCup A B₁ p (q + 1) (r + 1) (by omega) x (tateδ hS q y)
  let res₁ := tateRestrict H (A ⊗ᵣ B₁) (r + 1)
  have hc : tateδ hT r v = p.negOnePow • v' :=
    cupConnectingRight_signed_boundary A hS s h x y
  exact (tateRestrict_connecting H hT (Rep.tensorLeft_forget_splitting A s) r v).symm.trans
    ((congrArg res₁ hc).trans (restrictCup_sign H (A ⊗ᵣ B₁) p (r + 1) v'))

private theorem restrictCup_down_right_boundary (A B : Rep.{u} ℤ G) {p q r : ℤ}
    (h : p + q = r) (x : tate A p) (y : tate B q) :
    let hS := Rep.indShiftSequence_shortExact B
    let s := Rep.indShiftSequence_forget_splitting B
    let hT := Rep.tensorLeft_shortExact_of_forget_splitting A s
    let A' := Rep.res H.subtype A
    let B' := Rep.res H.subtype B
    let B₁' := Rep.res H.subtype (Rep.indShiftDown B)
    let xx := tateRestrict H A p x
    tateδ (subgroupRestrict_shortExact H hT) r
        (tateCup A' B' p q r h xx (tateRestrict H B q y)) =
      p.negOnePow • tateCup A' B₁' p (q + 1) (r + 1) (by omega) xx
        (tateRestrict H (Rep.indShiftDown B) (q + 1) (tateδ hS q y)) := by
  intro hS s hT A' B' B₁' xx
  let S := Rep.indShiftSequence B
  let F : Rep.{u} ℤ G ⥤ Rep.{u} ℤ H := Rep.resFunctor H.subtype
  let s' : ((S.map F).map (forget₂ (Rep.{u} ℤ H) (ModuleCat.{u} ℤ))).Splitting := s
  let hS' := subgroupRestrict_shortExact H hS
  let yy := tateRestrict H B q y
  let X := tate (A' ⊗ᵣ B₁') (r + 1)
  let f (v : tate B₁' (q + 1)) : X :=
    tateCup A' B₁' p (q + 1) (r + 1) (by omega) xx v
  have hboundary := cupConnectingRight_signed_boundary A' hS' s' h xx yy
  have hright := tateRestrict_connecting H hS s q y
  exact hboundary.trans (congrArg (fun v => p.negOnePow • f v) hright.symm)

private theorem restrictCup_step_down (A B : Rep.{u} ℤ G) {p q r : ℤ} (h : p + q = r)
    (x : tate A p) (y : tate B q)
    (ih : ∀ z : tate (Rep.indShiftDown B) (q + 1),
      tateRestrict H (A ⊗ᵣ Rep.indShiftDown B) (r + 1)
          (tateCup A (Rep.indShiftDown B) p (q + 1) (r + 1) (by omega) x z) =
        tateCup (Rep.res H.subtype A) (Rep.res H.subtype (Rep.indShiftDown B))
          p (q + 1) (r + 1) (by omega)
          (tateRestrict H A p x) (tateRestrict H (Rep.indShiftDown B) (q + 1) z)) :
    tateRestrict H (A ⊗ᵣ B) r (tateCup A B p q r h x y) =
      tateCup (Rep.res H.subtype A) (Rep.res H.subtype B) p q r h
        (tateRestrict H A p x) (tateRestrict H B q y) := by
  let S := Rep.indShiftSequence B
  let T := S.map (Rep.diagonalTensorLeft A)
  let F : Rep.{u} ℤ G ⥤ Rep.{u} ℤ H := Rep.resFunctor H.subtype
  let hS := Rep.indShiftSequence_shortExact B
  let s := Rep.indShiftSequence_forget_splitting B
  let hT := Rep.tensorLeft_shortExact_of_forget_splitting A s
  let hT' := subgroupRestrict_shortExact H hT
  have hz : IsZero (tate (T.map F).X₂ r) :=
    tate_resTensorIndBot_isZero H A (Rep.res (⊥ : Subgroup G).subtype B) r
  let B₁ := Rep.indShiftDown B
  let z := tateδ hS q y
  let X := tate (Rep.res H.subtype (A ⊗ᵣ B)) r
  let Y := tate (Rep.res H.subtype (A ⊗ᵣ B₁)) (r + 1)
  let signY (w : Y) : Y := p.negOnePow • w
  let δ : X ⟶ Y := tateδ hT' r
  have hδ : Function.Injective δ := tateδ_injective_of_isZero_middle hT' r hz
  have hL := restrictCup_down_left_boundary H A B h x y
  have hR := restrictCup_down_right_boundary H A B h x y
  exact hδ (hL.trans ((congrArg signY (ih z)).trans hR.symm))

/-- Subgroup restriction commutes with cup products in every integer bidegree. -/
theorem tateRestrict_cup (A : Rep.{u} ℤ G) (p q : ℤ) (x : tate A p) :
    ∀ (B : Rep.{u} ℤ G) (r : ℤ) (h : p + q = r) (y : tate B q),
      tateRestrict H (A ⊗ᵣ B) r (tateCup A B p q r h x y) =
        tateCup (Rep.res H.subtype A) (Rep.res H.subtype B) p q r h
          (tateRestrict H A p x) (tateRestrict H B q y) := by
  have hpos (i : ℕ) : ∀ (B : Rep.{u} ℤ G) (r : ℤ) (h : p + i = r) (y : tate B i),
      tateRestrict H (A ⊗ᵣ B) r (tateCup A B p i r h x y) =
        tateCup (Rep.res H.subtype A) (Rep.res H.subtype B) p i r h
          (tateRestrict H A p x) (tateRestrict H B i y) := by
    induction i with
    | zero =>
      intro B r h y
      have hr : r = p := h.symm.trans (add_zero p)
      revert h
      rw [hr]
      intro h
      have hAB := congrArg (fun f => tateRestrict H (A ⊗ᵣ B) p (f x y))
        (tateCup_zero_right A B p (add_zero p))
      have hR := congrArg (fun f => f (tateRestrict H A p x) (tateRestrict H B 0 y))
        (tateCup_zero_right (Rep.res H.subtype A) (Rep.res H.subtype B) p (add_zero p))
      exact hAB.trans ((tateRestrict_tensorCupZeroRight H A B p x y).trans hR.symm)
    | succ i ih =>
      intro B r h y
      obtain rfl : r = (p + i) + 1 := by omega
      exact restrictCup_step_up H A B (p := p) (q := i) (r := p + i) rfl x y
        (ih (Rep.coindShiftUp B) (p + i) rfl)
  cases q with
  | ofNat i => exact hpos i
  | negSucc i =>
    induction i with
    | zero =>
      intro B r h y
      exact restrictCup_step_down H A B h x y (hpos 0 (Rep.indShiftDown B) (r + 1) (by omega))
    | succ i ih =>
      intro B r h y
      exact restrictCup_step_down H A B h x y (ih (Rep.indShiftDown B) (r + 1) (by omega))

end IntegralGroupCohomology.Universe
