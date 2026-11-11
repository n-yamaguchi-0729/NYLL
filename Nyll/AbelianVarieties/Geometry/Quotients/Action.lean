/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Nyll.AbelianVarieties.Geometry.GroupLaw
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Action
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Quotient fibres and subgroup action relations

Prove connectedness of quotient fibres, the subgroup-action equivalence relation, and separatedness.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_connectedSpace_pullback_of_comp_eq_one_iff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.QuotientConnectedFibres


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace ConnectedFibres

variable {k : Type u} [Field k]

section grp

variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))

lemma mul_inv_mul_cancel (x y : SchemeHomOver t f) :
    L.mul t x (L.mul t (L.inv t x) y) = y := by
  rw [← L.mul_assoc, L.mul_inv_cancel, L.one_mul]


end grp

section main

variable {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G)
  {Q : Scheme.{u}} {fQ : Q ⟶ Spec (CommRingCat.of k)} (LQ : RelativeGroupLaw k fQ)
  (q : SchemeHomOver f fQ)
  (hq : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
      LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
  (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp x q = LQ.one t ↔
      ∃ y : SchemeHomOver t (i ≫ f),
        NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x)

include hq in
lemma comp_one_eq_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    NeronModelInfra.schemeHomOverComp (L.one t) q = LQ.one t :=
  AbelianVarieties.NOSProofs.KernelTorsor.Torsor.map_one L LQ q hq t

include hq in
lemma comp_inv_mul_eq_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t f)
    (h : NeronModelInfra.schemeHomOverComp x q = NeronModelInfra.schemeHomOverComp y q) :
    NeronModelInfra.schemeHomOverComp (L.mul t (L.inv t x) y) q = LQ.one t := by
  rw [hq, ← h, ← hq, L.inv_mul_cancel, comp_one_eq_one L LQ q hq]

include hq hker in
theorem connectedSpace_pullback [GeometricallyConnected (i ≫ f)] [Surjective q.1]
    {K : Type u} [Field K] (y : Spec (CommRingCat.of K) ⟶ Q) :
    ConnectedSpace ↑(pullback q.1 y) := by
  classical
  let F : Scheme.{u} := pullback q.1 y
  let prG : F ⟶ G := pullback.fst q.1 y
  let prK : F ⟶ Spec (CommRingCat.of K) := pullback.snd q.1 y
  have hcond : prG ≫ q.1 = prK ≫ y := pullback.condition
  have hqf : q.1 ≫ fQ = f := q.2
  obtain ⟨s0⟩ : Nonempty ↑(Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨p, -⟩ := prK.surjective s0
  let pt : Spec (F.residueField p) ⟶ F := F.fromSpecResidueField p
  let σ : Spec (F.residueField p) ⟶ Spec (CommRingCat.of k) := pt ≫ prK ≫ y ≫ fQ
  let NK : Scheme.{u} := pullback (i ≫ f) σ
  have hNK : ConnectedSpace ↑NK :=
    pullback_of_geometrically (GeometricallyConnected.geometrically_connectedSpace (f := i ≫ f))
      _ σ
  let tN : NK ⟶ Spec (CommRingCat.of k) := pullback.snd (i ≫ f) σ ≫ σ
  have hNcond : pullback.fst (i ≫ f) σ ≫ i ≫ f = pullback.snd (i ≫ f) σ ≫ σ := by
    simpa only [Category.assoc] using (pullback.condition (f := i ≫ f) (g := σ))
  let x1 : SchemeHomOver tN f :=
    ⟨pullback.snd (i ≫ f) σ ≫ pt ≫ prG, by
      simp only [tN, σ, Category.assoc, ← hqf]
      rw [reassoc_of% hcond]⟩
  let x2 : SchemeHomOver tN f := ⟨pullback.fst (i ≫ f) σ ≫ i, by
      simp only [tN, Category.assoc]; exact hNcond⟩
  have hx2 : NeronModelInfra.schemeHomOverComp x2 q = LQ.one tN := by
    refine (hker tN x2).mpr ⟨⟨pullback.fst (i ≫ f) σ, hNcond⟩, ?_⟩
    exact Subtype.ext rfl
  let θG : NK ⟶ G := (L.mul tN x1 x2).1
  have hθG : θG ≫ q.1 = (pullback.snd (i ≫ f) σ ≫ pt ≫ prK) ≫ y := by
    have h1 : θG ≫ q.1 = (NeronModelInfra.schemeHomOverComp (L.mul tN x1 x2) q).1 := rfl
    rw [h1, hq, hx2, LQ.mul_one]
    change (pullback.snd (i ≫ f) σ ≫ pt ≫ prG) ≫ q.1 = _
    simp only [Category.assoc, hcond]
  let θ : NK ⟶ F := pullback.lift θG (pullback.snd (i ≫ f) σ ≫ pt ≫ prK) hθG
  let FK : Scheme.{u} := pullback prK (pt ≫ prK)
  let π : FK ⟶ F := pullback.fst prK (pt ≫ prK)
  have hFKcond : π ≫ prK = pullback.snd prK (pt ≫ prK) ≫ pt ≫ prK := pullback.condition
  have hπ : Function.Surjective π := π.surjective
  let tF : FK ⟶ Spec (CommRingCat.of k) := π ≫ prK ≫ y ≫ fQ
  let uu : SchemeHomOver tF f := ⟨π ≫ prG, by
      simp only [tF, Category.assoc, ← hqf]
      rw [reassoc_of% hcond]⟩
  let pK : SchemeHomOver tF f := ⟨pullback.snd prK (pt ≫ prK) ≫ pt ≫ prG, by
      simp only [tF, Category.assoc, ← hqf]
      rw [reassoc_of% hcond, ← reassoc_of% hFKcond]⟩
  have hpu : NeronModelInfra.schemeHomOverComp pK q = NeronModelInfra.schemeHomOverComp uu q := by
    apply Subtype.ext
    change (pullback.snd prK (pt ≫ prK) ≫ pt ≫ prG) ≫ q.1 = (π ≫ prG) ≫ q.1
    simp only [Category.assoc, hcond]
    rw [← reassoc_of% hFKcond]
  have hx : NeronModelInfra.schemeHomOverComp (L.mul tF (L.inv tF pK) uu) q = LQ.one tF :=
    comp_inv_mul_eq_one L LQ q hq tF pK uu hpu
  obtain ⟨n, hn⟩ := (hker tF _).mp hx
  have hn1 : n.1 ≫ i = (L.mul tF (L.inv tF pK) uu).1 := congrArg Subtype.val hn
  have hψw : n.1 ≫ i ≫ f = pullback.snd prK (pt ≫ prK) ≫ σ := by
    rw [n.2]
    simp only [tF, σ]
    rw [← reassoc_of% hFKcond]
  let ψ : FK ⟶ NK := pullback.lift n.1 (pullback.snd prK (pt ≫ prK)) hψw
  have hψt : ψ ≫ tN = tF := by
    simp only [ψ, tN, pullback.lift_snd_assoc, tF, σ]
    rw [← reassoc_of% hFKcond]
  have hψθG : ψ ≫ θG = π ≫ prG := by
    have hnat := L.mul_natural tN tF ψ hψt x1 x2
    have e1 : GoodReductionJacobian.schemeHomOverComp ψ hψt x1 = pK := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, x1, pK, ψ, pullback.lift_snd_assoc]
    have e2 : GoodReductionJacobian.schemeHomOverComp ψ hψt x2 = L.mul tF (L.inv tF pK) uu := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, x2, ψ, pullback.lift_fst_assoc]
      exact hn1
    have hval := congrArg Subtype.val hnat
    rw [e1, e2, mul_inv_mul_cancel L tF pK uu] at hval
    simpa only [GoodReductionJacobian.schemeHomOverComp_coe] using hval
  have hψθ : ψ ≫ θ = π := by
    apply pullback.hom_ext
    · simp only [θ, Category.assoc, pullback.lift_fst]
      exact hψθG
    · simp only [θ, Category.assoc, pullback.lift_snd]
      simp only [ψ, pullback.lift_snd_assoc]
      exact hFKcond.symm
  have hθ : Function.Surjective θ := by
    intro z
    obtain ⟨w, rfl⟩ := hπ z
    exact ⟨ψ w, by rw [← Scheme.Hom.comp_apply, hψθ]⟩
  exact hθ.connectedSpace θ.continuous

include hq hker in
theorem geometricallyConnected [GeometricallyConnected (i ≫ f)] [Surjective q.1] :
    GeometricallyConnected q.1 := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have : ConnectedSpace ↑(pullback q.1 y) := connectedSpace_pullback L i LQ q hq hker y
  exact (h.isoPullback.inv.surjective).connectedSpace h.isoPullback.inv.continuous

include hq hker in
theorem connectedSpace_preimage [GeometricallyConnected (i ≫ f)] [Surjective q.1]
    (h : ℕ) [SmoothOfRelativeDimension h q.1]
    {M : Scheme.{u}} (j : M ⟶ Q) [ConnectedSpace ↑M] :
    ConnectedSpace ↑(pullback j q.1) := by
  have : GeometricallyConnected q.1 := geometricallyConnected L i LQ q hq hker
  have : Smooth q.1 := SmoothOfRelativeDimension.smooth h q.1
  have : UniversallyOpen q.1 := inferInstance
  infer_instance

end main

end ConnectedFibres

theorem _root_.GoodReductionJacobian.RelativeGroupLaw.connectedSpace_pullback_of_comp_eq_one_iff
    (k : Type u) [Field k]
    {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i]
    {Q : Scheme.{u}} (fQ : Q ⟶ Spec (CommRingCat.of k)) (LQ : RelativeGroupLaw k fQ)
    (q : SchemeHomOver f fQ)
    (hq : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
        LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp x q = LQ.one t ↔
        ∃ y : SchemeHomOver t (i ≫ f),
          NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x)
    [IsAffine N] [GeometricallyConnected (i ≫ f)]
    (h : ℕ) [SmoothOfRelativeDimension h q.1] [Surjective q.1] [QuasiCompact q.1]
    {M : Scheme.{u}} (j : M ⟶ Q) [IsClosedImmersion j] [ConnectedSpace M] :
    ConnectedSpace ↥(pullback q.1 j) := by
  have : GeometricallyConnected q.1 := ConnectedFibres.geometricallyConnected L i LQ q hq hker
  have : Smooth q.1 := SmoothOfRelativeDimension.smooth h q.1
  have : UniversallyOpen q.1 := inferInstance
  infer_instance

end AbelianVarieties.NOSProofs.QuotientConnectedFibres
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_action_shear_and_equivalence_of_isClosedImmersion.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.QuotientEquivalence


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace SubgroupAction

open GoodReductionJacobian.RelativeGroupLaw

variable {R : Type u} [CommRing R] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)}


theorem mul_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of
    R)} (h : t = t')
    (v w : T ⟶ G) (hv : v ≫ f = t) (hw : w ≫ f = t) (hv' : v ≫ f = t') (hw' : w ≫ f = t') :
    (L.mul t ⟨v, hv⟩ ⟨w, hw⟩).1 = (L.mul t' ⟨v, hv'⟩ ⟨w, hw'⟩).1 := by
  subst h; rfl

theorem inv_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of
    R)} (h : t = t')
    (v : T ⟶ G) (hv : v ≫ f = t) (hv' : v ≫ f = t') :
    (L.inv t ⟨v, hv⟩).1 = (L.inv t' ⟨v, hv'⟩).1 := by
  subst h; rfl

variable (L : RelativeGroupLaw R f) {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw R (i ≫ f))

theorem hom_one
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    NeronModelInfra.schemeHomOverComp (LN.one t) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = L.one t :=
  AbelianVarieties.NOSProofs.KernelTorsor.Torsor.map_one LN L ⟨i, rfl⟩ hi t

theorem hom_inv
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : SchemeHomOver t (i ≫ f)) :
    NeronModelInfra.schemeHomOverComp (LN.inv t n) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
      L.inv t (NeronModelInfra.schemeHomOverComp n (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)) :=
  AbelianVarieties.NOSProofs.KernelTorsor.Torsor.map_inv LN L ⟨i, rfl⟩ hi t n

theorem comp_action {T : Scheme.{u}} (φ : T ⟶ pullback (i ≫ f) f) :
    φ ≫ L.action i =
      (L.mul (φ ≫ actionSource f i)
        (GoodReductionJacobian.schemeHomOverComp φ rfl (L.actionFstPoint i))
        (GoodReductionJacobian.schemeHomOverComp φ rfl (L.actionSndPoint i))).1 :=
  congrArg Subtype.val (L.mul_natural _ _ φ rfl (L.actionFstPoint i) (L.actionSndPoint i))

theorem comp_action' {T : Scheme.{u}} (φ : T ⟶ pullback (i ≫ f) f) (t : T ⟶ Spec (CommRingCat.of R))
    (ht : φ ≫ actionSource f i = t) :
    φ ≫ L.action i =
      (L.mul t ⟨φ ≫ pullback.fst (i ≫ f) f ≫ i, by rw [← ht, Category.assoc, Category.assoc,
        pullback.condition]⟩
        ⟨φ ≫ pullback.snd (i ≫ f) f, by rw [← ht, Category.assoc]⟩).1 := by
  rw [comp_action L i φ]
  exact mul_val_congr L ht _ _ _ _ _ _


end SubgroupAction

end

open SubgroupAction GoodReductionJacobian.RelativeGroupLaw in
theorem
    _root_.GoodReductionJacobian.RelativeGroupLaw.action_shear_and_equivalence_of_isClosedImmersion
    {R : Type u} [CommRing R] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L :
      RelativeGroupLaw R f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw R (i ≫ f))
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) :
    L.action i ≫ f = CategoryTheory.Limits.pullback.snd (i ≫ f) f ≫ f ∧
    (∃ σ : CategoryTheory.Limits.pullback (i ≫ f) f ≅ CategoryTheory.Limits.pullback (i ≫ f) f,
      σ.hom ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f = L.action i ∧
      σ.hom ≫ CategoryTheory.Limits.pullback.fst (i ≫ f) f = CategoryTheory.Limits.pullback.fst (i ≫
        f) f) ∧
    (∀ {T : Scheme.{u}} (a b : T ⟶ CategoryTheory.Limits.pullback (i ≫ f) f),
      a ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f = b ≫ CategoryTheory.Limits.pullback.snd (i ≫
        f) f → a ≫ L.action i = b ≫ L.action i → a = b) ∧
    (∀ T : Scheme.{u}, _root_.Equivalence fun x y : T ⟶ G =>
      ∃ φ : T ⟶ CategoryTheory.Limits.pullback (i ≫ f) f, φ ≫ CategoryTheory.Limits.pullback.snd (i
        ≫ f) f = x ∧ φ ≫ L.action i = y) := by
  obtain ⟨σ, hσfst, hσsnd⟩ :=
    L.exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul (i ≫ f) ⟨i, rfl⟩
  have hσaction : σ.hom ≫ pullback.snd (i ≫ f) f = L.action i := by
    rw [hσsnd, L.action_def]
    exact mul_val_congr L (pullback.condition (f := i ≫ f) (g := f)) _ _ _ _ _ _
  refine ⟨L.action_over i, ⟨σ, hσaction, hσfst⟩, ?_, ?_⟩
  · intro T a b hs ht
    apply pullback.hom_ext _ hs
    let t : T ⟶ Spec (CommRingCat.of R) := a ≫ actionSource f i
    have hbt : b ≫ actionSource f i = t := by
      change b ≫ pullback.snd (i ≫ f) f ≫ f = a ≫ pullback.snd (i ≫ f) f ≫ f
      rw [← Category.assoc, ← hs, Category.assoc]
    rw [comp_action' L i a t rfl, comp_action' L i b t hbt] at ht
    let : Group (SchemeHomOver t f) := L.pointGroup t
    have hx : (⟨b ≫ pullback.snd (i ≫ f) f, by rw [← hbt, Category.assoc]⟩ : SchemeHomOver t f) =
        ⟨a ≫ pullback.snd (i ≫ f) f, by rw [Category.assoc]⟩ := Subtype.ext hs.symm
    rw [hx] at ht
    have := mul_right_cancel (G := SchemeHomOver t f) (Subtype.ext ht)
    have h1 : (a ≫ pullback.fst (i ≫ f) f) ≫ i = (b ≫ pullback.fst (i ≫ f) f) ≫ i := by
      simpa only [Category.assoc] using congrArg Subtype.val this
    exact (cancel_mono i).mp h1
  · intro T
    refine ⟨fun x => ?_, fun {x y} hxy => ?_, fun {x y z} hxy hyz => ?_⟩
    · refine ⟨pullback.lift (LN.one (x ≫ f)).1 x (LN.one (x ≫ f)).2, pullback.lift_snd _ _ _, ?_⟩
      rw [comp_action' L i _ (x ≫ f) (by
        change pullback.lift (LN.one (x ≫ f)).1 x (LN.one (x ≫ f)).2 ≫ pullback.snd (i ≫ f) f ≫ f =
          x ≫ f
        rw [← Category.assoc, pullback.lift_snd])]
      have key : L.mul (x ≫ f) (NeronModelInfra.schemeHomOverComp (LN.one (x ≫ f)) ⟨i, rfl⟩) ⟨x,
        rfl⟩ = ⟨x, rfl⟩ := by
        rw [hom_one L i LN hi, L.one_mul]
      refine Eq.trans ?_ (congrArg Subtype.val key)
      congr 2 <;> apply Subtype.ext
      · change pullback.lift (LN.one (x ≫ f)).1 x _ ≫ pullback.fst (i ≫ f) f ≫ i = (LN.one (x ≫
        f)).1 ≫ i
        rw [← Category.assoc, pullback.lift_fst]
      · exact pullback.lift_snd _ _ _
    · obtain ⟨φ, rfl, rfl⟩ := hxy
      let t : T ⟶ Spec (CommRingCat.of R) := φ ≫ actionSource f i
      let n : SchemeHomOver t (i ≫ f) := ⟨φ ≫ pullback.fst (i ≫ f) f, by
        change (φ ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f = φ ≫ pullback.snd (i ≫ f) f ≫ f
        rw [Category.assoc, pullback.condition]⟩
      let x : SchemeHomOver t f := ⟨φ ≫ pullback.snd (i ≫ f) f, by rw [Category.assoc]⟩
      have hact : φ ≫ L.action i = (L.mul t (NeronModelInfra.schemeHomOverComp n ⟨i, rfl⟩) x).1 :=
        (comp_action' L i φ t rfl).trans (mul_val_congr L rfl _ _ _ _ _ _)
      refine ⟨pullback.lift (LN.inv t n).1 (φ ≫ L.action i)
        (by rw [(LN.inv t n).2, Category.assoc, L.action_over]), pullback.lift_snd _ _ _, ?_⟩
      have hsrc : pullback.lift (LN.inv t n).1 (φ ≫ L.action i)
          (by rw [(LN.inv t n).2, Category.assoc, L.action_over]) ≫ actionSource f i = t := by
        change _ ≫ pullback.snd (i ≫ f) f ≫ f = t
        rw [← Category.assoc, pullback.lift_snd, Category.assoc, L.action_over]
      rw [comp_action' L i _ t hsrc]
      have key : L.mul t (NeronModelInfra.schemeHomOverComp (LN.inv t n) ⟨i, rfl⟩)
          (L.mul t (NeronModelInfra.schemeHomOverComp n ⟨i, rfl⟩) x) = x := by
        rw [hom_inv L i LN hi, ← L.mul_assoc, L.inv_mul_cancel, L.one_mul]
      refine Eq.trans ?_ (congrArg Subtype.val key)
      congr 2 <;> apply Subtype.ext
      · change pullback.lift (LN.inv t n).1 (φ ≫ L.action i) _ ≫ pullback.fst (i ≫ f) f ≫ i =
        (LN.inv t n).1 ≫ i
        rw [← Category.assoc, pullback.lift_fst]
      · change pullback.lift (LN.inv t n).1 (φ ≫ L.action i) _ ≫ pullback.snd (i ≫ f) f = (L.mul t _
        x).1
        rw [pullback.lift_snd, hact]
    · obtain ⟨φ, rfl, rfl⟩ := hxy
      obtain ⟨ψ, hψ, rfl⟩ := hyz
      let t : T ⟶ Spec (CommRingCat.of R) := φ ≫ actionSource f i
      let n₁ : SchemeHomOver t (i ≫ f) := ⟨φ ≫ pullback.fst (i ≫ f) f, by
        change (φ ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f = φ ≫ pullback.snd (i ≫ f) f ≫ f
        rw [Category.assoc, pullback.condition]⟩
      let x : SchemeHomOver t f := ⟨φ ≫ pullback.snd (i ≫ f) f, by rw [Category.assoc]⟩
      have hψt : ψ ≫ actionSource f i = t := by
        change ψ ≫ pullback.snd (i ≫ f) f ≫ f = t
        rw [← Category.assoc, hψ, Category.assoc, L.action_over]
      let n₂ : SchemeHomOver t (i ≫ f) := ⟨ψ ≫ pullback.fst (i ≫ f) f, by
        rw [← hψt]
        change (ψ ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f = ψ ≫ pullback.snd (i ≫ f) f ≫ f
        rw [Category.assoc, pullback.condition]⟩
      have hact1 : φ ≫ L.action i = (L.mul t (NeronModelInfra.schemeHomOverComp n₁ ⟨i, rfl⟩) x).1 :=
        (comp_action' L i φ t rfl).trans (mul_val_congr L rfl _ _ _ _ _ _)
      have hact2 : ψ ≫ L.action i = (L.mul t (NeronModelInfra.schemeHomOverComp n₂ ⟨i, rfl⟩)
          (L.mul t (NeronModelInfra.schemeHomOverComp n₁ ⟨i, rfl⟩) x)).1 := by
        rw [comp_action' L i ψ t hψt]
        congr 2
        apply Subtype.ext
        change ψ ≫ pullback.snd (i ≫ f) f = _
        rw [hψ, hact1]
      refine ⟨pullback.lift (LN.mul t n₂ n₁).1 (φ ≫ pullback.snd (i ≫ f) f)
        (by rw [(LN.mul t n₂ n₁).2, Category.assoc]), pullback.lift_snd _ _ _, ?_⟩
      have hsrc : pullback.lift (LN.mul t n₂ n₁).1 (φ ≫ pullback.snd (i ≫ f) f)
          (by rw [(LN.mul t n₂ n₁).2, Category.assoc]) ≫ actionSource f i = t := by
        change _ ≫ pullback.snd (i ≫ f) f ≫ f = t
        rw [← Category.assoc, pullback.lift_snd, Category.assoc]
      rw [comp_action' L i _ t hsrc, hact2, ← L.mul_assoc, ← hi]
      congr 2 <;> apply Subtype.ext
      · change pullback.lift (LN.mul t n₂ n₁).1 _ _ ≫ pullback.fst (i ≫ f) f ≫ i = (LN.mul t n₂
        n₁).1 ≫ i
        rw [← Category.assoc, pullback.lift_fst]
      · exact pullback.lift_snd _ _ _

end AbelianVarieties.NOSProofs.QuotientEquivalence
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isSeparated_and_quasiCompact_of_isPullback_action_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.QuotientSeparatedness


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace ProductShear

variable {R : Type u} [CommRing R] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)}

theorem inv_natural (L : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) = L.inv t'
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) :=
  L.inv_natural t t' ψ hψ x

/-- The structure map of the product of the group with itself. -/
abbrev τ (f : G ⟶ Spec (CommRingCat.of R)) : pullback f f ⟶ Spec (CommRingCat.of R) := pullback.snd
    f f ≫ f

/-- The first group point on the product. -/
def pa (f : G ⟶ Spec (CommRingCat.of R)) : SchemeHomOver (τ f) f := ⟨pullback.fst f f,
    pullback.condition⟩
/-- The second group point on the product. -/
def pb (f : G ⟶ Spec (CommRingCat.of R)) : SchemeHomOver (τ f) f := ⟨pullback.snd f f, rfl⟩

/-- Send a pair to its second coordinate and its product. -/
def shearHom (L : RelativeGroupLaw R f) : pullback f f ⟶ pullback f f :=
  pullback.lift (pullback.snd f f) (L.mul (τ f) (pa f) (pb f)).1 (by rw [(L.mul (τ f) (pa f) (pb
    f)).2])

/-- Recover the pair by division using the first coordinate. -/
def shearInv (L : RelativeGroupLaw R f) : pullback f f ⟶ pullback f f :=
  pullback.lift (L.mul (τ f) (pb f) (L.inv (τ f) (pa f))).1 (pullback.fst f f)
    (by rw [(L.mul (τ f) (pb f) (L.inv (τ f) (pa f))).2]; exact pullback.condition.symm)

@[scoped simp]
theorem shearHom_fst (L : RelativeGroupLaw R f) : shearHom L ≫ pullback.fst f f = pullback.snd f f
    :=
  pullback.lift_fst _ _ _
@[scoped simp]
theorem shearHom_snd (L : RelativeGroupLaw R f) :
    shearHom L ≫ pullback.snd f f = (L.mul (τ f) (pa f) (pb f)).1 := pullback.lift_snd _ _ _
@[scoped simp]
theorem shearInv_fst (L : RelativeGroupLaw R f) :
    shearInv L ≫ pullback.fst f f = (L.mul (τ f) (pb f) (L.inv (τ f) (pa f))).1 := pullback.lift_fst
      _ _ _
@[scoped simp]
theorem shearInv_snd (L : RelativeGroupLaw R f) : shearInv L ≫ pullback.snd f f = pullback.fst f f
    :=
  pullback.lift_snd _ _ _

theorem shearHom_τ (L : RelativeGroupLaw R f) : shearHom L ≫ τ f = τ f := by
  change shearHom L ≫ pullback.snd f f ≫ f = pullback.snd f f ≫ f
  rw [← Category.assoc, shearHom_snd, (L.mul (τ f) (pa f) (pb f)).2]

theorem shearInv_τ (L : RelativeGroupLaw R f) : shearInv L ≫ τ f = τ f := by
  change shearInv L ≫ pullback.snd f f ≫ f = pullback.snd f f ≫ f
  rw [← Category.assoc, shearInv_snd, pullback.condition]

/-- The product-coordinate transformation as an isomorphism. -/
def shear (L : RelativeGroupLaw R f) : pullback f f ≅ pullback f f where
  hom := shearHom L
  inv := shearInv L
  hom_inv_id := by
    have ha : GoodReductionJacobian.schemeHomOverComp (shearHom L) (shearHom_τ L) (pa f) = pb f :=
      Subtype.ext (shearHom_fst L)
    have hb : GoodReductionJacobian.schemeHomOverComp (shearHom L) (shearHom_τ L) (pb f) = L.mul (τ
      f) (pa f) (pb f) :=
      Subtype.ext (shearHom_snd L)
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, shearInv_fst]
      have := congrArg Subtype.val
        (L.mul_natural (τ f) (τ f) (shearHom L) (shearHom_τ L) (pb f) (L.inv (τ f) (pa f)))
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
      rw [this, inv_natural, ha, hb, L.mul_assoc, L.mul_inv_cancel, L.mul_one]
      rfl
    · rw [Category.id_comp, Category.assoc, shearInv_snd, shearHom_fst]
  inv_hom_id := by
    have ha : GoodReductionJacobian.schemeHomOverComp (shearInv L) (shearInv_τ L) (pa f) =
        L.mul (τ f) (pb f) (L.inv (τ f) (pa f)) := Subtype.ext (shearInv_fst L)
    have hb : GoodReductionJacobian.schemeHomOverComp (shearInv L) (shearInv_τ L) (pb f) = pa f :=
      Subtype.ext (shearInv_snd L)
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, shearHom_fst, shearInv_snd]
    · rw [Category.id_comp, Category.assoc, shearHom_snd]
      have := congrArg Subtype.val (L.mul_natural (τ f) (τ f) (shearInv L) (shearInv_τ L) (pa f) (pb
        f))
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
      rw [this, ha, hb, L.mul_assoc, L.inv_mul_cancel, L.mul_one]
      rfl

theorem lift_snd_action_eq (L : RelativeGroupLaw R f) {N : Scheme.{u}} (i : N ⟶ G)
    (hst : pullback.snd (i ≫ f) f ≫ f = L.action i ≫ f) :
    pullback.lift (pullback.snd (i ≫ f) f) (L.action i) hst =
      pullback.map (i ≫ f) f f f i (𝟙 G) (𝟙 _) ((Category.comp_id _).trans rfl) ((Category.comp_id
        _).trans (Category.id_comp _).symm) ≫
        (shear L).hom := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc]
    change _ = _ ≫ shearHom L ≫ _
    rw [shearHom_fst, pullback.lift_snd, Category.comp_id]
  · rw [pullback.lift_snd, Category.assoc]
    change _ = _ ≫ shearHom L ≫ _
    rw [shearHom_snd]
    set m := pullback.map (i ≫ f) f f f i (𝟙 G) (𝟙 _) ((Category.comp_id _).trans rfl)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    have hm : m ≫ τ f = GoodReductionJacobian.RelativeGroupLaw.actionSource f i := by
      change m ≫ pullback.snd f f ≫ f = pullback.snd (i ≫ f) f ≫ f
      rw [← Category.assoc, pullback.lift_snd, Category.comp_id]
    have := congrArg Subtype.val (L.mul_natural (τ f)
      (GoodReductionJacobian.RelativeGroupLaw.actionSource f i) m hm (pa f) (pb f))
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
    rw [this, L.action_def]
    congr 2
    · apply Subtype.ext
      change pullback.fst (i ≫ f) f ≫ i = m ≫ pullback.fst f f
      exact (pullback.lift_fst _ _ _).symm
    · apply Subtype.ext
      change pullback.snd (i ≫ f) f = m ≫ pullback.snd f f
      exact ((pullback.lift_snd _ _ _).trans (Category.comp_id _)).symm

end ProductShear

end

end AbelianVarieties.NOSProofs.QuotientSeparatedness

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

open AbelianVarieties.NOSProofs.QuotientSeparatedness.ProductShear in
theorem isSeparated_and_quasiCompact_of_isPullback_action_of_surjective
    (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i]
    {Q : Scheme.{u}} (fQ : Q ⟶ Spec (CommRingCat.of k)) (q : G ⟶ Q) (hq : q ≫ fQ = f)
    [Flat q] [LocallyOfFinitePresentation q] [QuasiCompact q] [Surjective q]
    (hR : IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f) (L.action i) q q) :
    IsSeparated fQ ∧ QuasiCompact fQ := by
  constructor
  · subst hq
    have hst : pullback.snd (i ≫ q ≫ fQ) (q ≫ fQ) ≫ q ≫ fQ = L.action i ≫ q ≫ fQ := by
      have := congrArg (fun φ => φ ≫ fQ) hR.w
      simpa only [Category.assoc] using this
    let π := pullback.map (q ≫ fQ) (q ≫ fQ) fQ fQ q q (𝟙 _) (Category.comp_id _) (Category.comp_id
      _)
    let ρ := pullback.map q q (q ≫ fQ) (q ≫ fQ) (𝟙 G) (𝟙 G) fQ (Category.id_comp _).symm
      (Category.id_comp _).symm
    have hΔ := pullback_map_diagonal_isPullback q q fQ
    have : Flat π := MorphismProperty.pullbackMap (P := @Flat) inferInstance inferInstance rfl rfl
    have : QuasiCompact π := MorphismProperty.pullbackMap (P := @QuasiCompact) inferInstance
      inferInstance rfl rfl
    have : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
      (inferInstance : MorphismProperty.IsMultiplicative
        (fun {_ _ : Scheme.{u}} h => Surjective h)).toIsStableUnderComposition
    have : Surjective π := MorphismProperty.pullbackMap (P := @Surjective.{u}) inferInstance
      inferInstance rfl rfl
    have hquot := Flat.isQuotientMap_of_surjective π
    have h1 : Set.range ρ.base = π.base ⁻¹' Set.range (pullback.diagonal fQ).base := by
      have := AlgebraicGeometry.Scheme.image_preimage_eq_of_isPullback hΔ Set.univ
      simpa only [Set.preimage_univ, Set.image_univ] using this
    have h2 : pullback.lift (pullback.snd (i ≫ q ≫ fQ) (q ≫ fQ)) (L.action i) hst =
      hR.isoPullback.hom ≫ ρ := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, Category.comp_id,
        IsPullback.isoPullback_hom_fst]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id,
        IsPullback.isoPullback_hom_snd]
    have : IsClosedImmersion (pullback.lift (pullback.snd (i ≫ q ≫ fQ) (q ≫ fQ)) (L.action i) hst)
      := by
      rw [lift_snd_action_eq L i hst]
      have : MorphismProperty.IsStableUnderComposition (@IsClosedImmersion.{u}) :=
        (inferInstance : MorphismProperty.IsMultiplicative
          (fun {_ _ : Scheme.{u}} h => IsClosedImmersion h)).toIsStableUnderComposition
      have : IsClosedImmersion (pullback.map (i ≫ q ≫ fQ) (q ≫ fQ) (q ≫ fQ) (q ≫ fQ) i (𝟙 G) (𝟙 _)
          ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans (Category.id_comp _).symm))
            :=
        MorphismProperty.pullbackMap (P := @IsClosedImmersion.{u}) inferInstance inferInstance rfl
          (Category.id_comp _).symm
      infer_instance
    have h3 : IsClosed (Set.range ρ.base) := by
      have hr : Set.range (pullback.lift (pullback.snd (i ≫ q ≫ fQ) (q ≫ fQ)) (L.action i) hst).base
        = Set.range ρ.base := by
        rw [h2, Scheme.Hom.comp_base, TopCat.coe_comp]
        exact (hR.isoPullback.hom.homeomorph.surjective).range_comp _
      rw [← hr]
      exact (Scheme.Hom.isClosedEmbedding _).isClosed_range
    have h4 : IsClosed (Set.range (pullback.diagonal fQ).base) := by
      rw [← hquot.isClosed_preimage, ← h1]; exact h3
    exact ⟨IsClosedImmersion.of_isPreimmersion _ h4⟩
  · have : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace f
    have : CompactSpace Q := ⟨by
      rw [← Set.range_eq_univ.mpr q.surjective]
      exact isCompact_range q.continuous⟩
    exact quasiCompact_of_compactSpace fQ

end GoodReductionJacobian.RelativeGroupLaw
end
