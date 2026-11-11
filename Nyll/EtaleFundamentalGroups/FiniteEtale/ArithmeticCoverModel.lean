/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.SubalgebraStagesIsLimitCone
public import Nyll.SchemeTheory.Descent.IntegerSubalgebraModels
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitFiniteFamily
public import Nyll.EtaleFundamentalGroups.GaloisCovers.SelfProduct
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
public import Nyll.SchemeTheory.Descent.FgSubalgebraPullbackFinitePresentation
public import Nyll.SchemeTheory.Descent.FgSubalgebraProperFlatPullback
public import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyConnectedFgSubalgebra
public import Nyll.AlgebraicCurves.Models.Construction.SmoothOpenCompactification
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Nyll.SchemeTheory.Descent.FgSubalgebraHomPullback
public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.ClosedImmersionFiniteSubalgebra
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackIdentity
public import Nyll.GaloisCohomology.FieldTheory.FiniteTypeClosedResidue
public import Nyll.GaloisCohomology.FieldTheory.NormalArithmeticSubalgebra
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Nyll.GaloisCohomology.FieldTheory.FinitelyGeneratedModel
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-!
# Finite-residue arithmetic models of an original finite étale cover

A specified finite étale cover of the generic fibre of an arithmetic family
spreads to an actual finitely generated coefficient enlargement. The same
enlargement contains field generators and the inverse of a prescribed degree
and auxiliary primes. Its closed points have finite residue fields of allowed
characteristic. The comparison retains the original cover and the native
Cartesian generic-fibre map; no properness or abelianity is required.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicCurves.Geometry.Curves.Proofs
open GeometricallyConnected_exists_fg_subalgebra_of_geometricallyConnected_pullback_snd

namespace AlgebraicGeometry.FiniteEtale

attribute [local instance] SubalgebraStages.compactSpace_obj
  SubalgebraStages.quasiSeparatedSpace_obj SubalgebraStages.isAffineHom_diagram_map
  SubalgebraStages.quasiCompact_snd SubalgebraStages.quasiSeparated_snd
  SubalgebraStages.isCofiltered_op

/-- An original finite étale generic cover and its specified finite group
action spread to one finite-type arithmetic model. All original group labels
and their multiplication equations are retained, and faithful actions stay
faithful. Surjective covers remain surjective, and an invertible original
graph pairing remains invertible.
The prescribed nonzero degree is a unit and the finite residue
characteristic avoids the specified finite set. -/
theorem exists_arithmetic_cover_action_model_finite_residue_with_graph
    (K : Type u) [Field K] [CharZero K] [Field.FG K]
    (S₀ : Subalgebra ℤ K) (hS₀ : S₀.FG)
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of S₀)) [QuasiCompact f₀] [QuasiSeparated f₀]
    (W : FiniteEtale (Limits.pullback f₀
      (Spec.map (CommRingCat.ofHom (algebraMap S₀ K)))))
    {G : Type v} [Group G] [Finite G] (ρ : G →* Aut W)
    (n : ℕ) (hn : n ≠ 0) (Sigma : Finset ℕ) :
    ∃ T : Subalgebra S₀ K, T.FG ∧ IsFractionRing T K ∧ IsUnit (n : T) ∧
      ∃ m : Ideal T, m.IsMaximal ∧ Finite (T ⧸ m) ∧
        (ringChar (T ⧸ m)).Prime ∧ ringChar (T ⧸ m) ∉ Sigma ∧
        ¬ ringChar (T ⧸ m) ∣ n ∧
        ∃ (V : FiniteEtale (Limits.pullback f₀
            (Spec.map (CommRingCat.ofHom (algebraMap S₀ T)))))
          (p : Limits.pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))) ⟶
            Limits.pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ T)))),
          IsPullback p
            (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))))
            (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ T))))
            (Spec.map (CommRingCat.ofHom T.val.toRingHom)) ∧
          p ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ T))) =
            Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))) ∧
          ∃ (e : (FiniteEtale.pullback p).obj V ≅ W) (ρV : G →* Aut V),
            (Function.Injective ρ → Function.Injective ρV) ∧
            (Surjective W.hom → Surjective V.hom) ∧
            (IsIso (graphFamilyMap (fun g : G => (ρ g).asIso.hom)) →
              IsIso (graphFamilyMap (fun g : G => (ρV g).asIso.hom))) ∧ ∀ g : G,
              (FiniteEtale.pullback p).map (ρV g).asIso.hom ≫ e.hom =
                e.hom ≫ (ρ g).asIso.hom := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Field.FG K).finitely_generated
  let primes := Sigma.filter Nat.Prime
  let aux := primes.prod id
  have haux : aux ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun q hq =>
    (Finset.mem_filter.mp hq).2.ne_zero)
  let ell := n * aux
  have hell : ell ≠ 0 := Nat.mul_ne_zero hn haux
  let seed := insert ((ell : K)⁻¹) s
  let S : Finset K →o Subalgebra S₀ K :=
    { toFun := fun i => Algebra.adjoin S₀ (↑(i ∪ seed) : Set K)
      monotone' := fun i j hij => Algebra.adjoin_mono (by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact Finset.mem_union.mpr (Or.inl (hij hx))
        · exact Finset.mem_union.mpr (Or.inr hx)) }
  have hcover (x : K) : ∃ i : Finset K, x ∈ S i :=
    ⟨{x}, Algebra.subset_adjoin (Finset.mem_union.mpr
      (Or.inl (Finset.mem_singleton_self x)))⟩
  let D := SubalgebraStages.diagram S f₀
  let c := SubalgebraStages.cone S f₀
  obtain ⟨hc⟩ := SubalgebraStages.nonempty_isLimit_cone S hcover f₀
  obtain ⟨i, V, e, ρV, hsurj, hgraph, hρV⟩ :=
    exists_inverse_limit_model_finite_action_with_cover D c hc W ρ
  have hinj (hρ : Function.Injective ρ) : Function.Injective ρV := by
    intro g h hgh
    apply hρ
    apply Aut.ext
    apply Iso.ext
    apply (cancel_epi e.hom).mp
    rw [← hρV g, ← hρV h, hgh]
  let T := S i.unop
  have hT : T.FG := Subalgebra.fg_adjoin_finset (i.unop ∪ seed)
  have hseed {x : K} (hx : x ∈ seed) : x ∈ T :=
    Algebra.subset_adjoin (Finset.mem_union.mpr (Or.inr hx))
  have hfrac : IsFractionRing T K := by
    apply IsFractionRing.of_field T K
    intro z
    have hz : z ∈ Subfield.closure (s : Set K) := by
      rw [hs]
      exact Subfield.mem_top z
    obtain ⟨b, hb, d, hd, hbd⟩ := Subfield.mem_closure_iff.mp hz
    have hsub : Subring.closure (s : Set K) ≤ T.toSubring :=
      Subring.closure_le.mpr (fun x hx => hseed (Finset.mem_insert_of_mem hx))
    exact ⟨⟨b, hsub hb⟩, ⟨d, hsub hd⟩, hbd.symm⟩
  have hellK : (ell : K) ≠ 0 := Nat.cast_ne_zero.mpr hell
  have hunit : IsUnit (ell : T) := by
    refine ⟨{
      val := (ell : T)
      inv := ⟨(ell : K)⁻¹, hseed (Finset.mem_insert_self _ _)⟩
      val_inv := ?_
      inv_val := ?_ }, rfl⟩
    · apply Subtype.ext
      exact mul_inv_cancel₀ hellK
    · apply Subtype.ext
      exact inv_mul_cancel₀ hellK
  have hnT : IsUnit (n : T) := by
    have hmul : IsUnit ((n : T) * (aux : T)) := by
      simpa only [ell, Nat.cast_mul] using hunit
    exact isUnit_of_mul_isUnit_left hmul
  have : Algebra.FiniteType ℤ S₀ := (Subalgebra.fg_iff_finiteType S₀).mp hS₀
  have : Algebra.FiniteType S₀ T := (Subalgebra.fg_iff_finiteType T).mp hT
  have : Algebra.FiniteType ℤ T := Algebra.FiniteType.trans
    (R := ℤ) (S := S₀) (A := T) inferInstance inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal T
  have : m.IsMaximal := hm
  let : Field (T ⧸ m) := Ideal.Quotient.field m
  have hfinite : Finite (T ⧸ m) := FieldTheory.finite_quotient_of_finiteType_int T m
  have : Algebra.FiniteType ℤ (T ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mk m).toIntAlgHom
      Ideal.Quotient.mk_surjective
  have hchar : ringChar (T ⧸ m) ≠ 0 := FieldTheory.ringChar_ne_zero_of_finiteType_int (T ⧸ m)
  have hprime : (ringChar (T ⧸ m)).Prime :=
    (CharP.char_is_prime_or_zero (T ⧸ m) (ringChar (T ⧸ m))).resolve_right hchar
  have hnotdvd : ¬ ringChar (T ⧸ m) ∣ ell := by
    intro hdvd
    have hu : IsUnit (ell : T ⧸ m) := by
      simpa only [map_natCast] using hunit.map (Ideal.Quotient.mk m)
    exact hu.ne_zero ((CharP.cast_eq_zero_iff (T ⧸ m) (ringChar (T ⧸ m)) ell).mpr hdvd)
  have hpSigma : ringChar (T ⧸ m) ∉ Sigma := by
    intro hp
    exact hnotdvd (dvd_mul_of_dvd_right
      (Finset.dvd_prod_of_mem id (Finset.mem_filter.mpr ⟨hp, hprime⟩)) n)
  have hpn : ¬ ringChar (T ⧸ m) ∣ n := fun h =>
    hnotdvd (dvd_mul_of_dvd_left h aux)
  exact ⟨T, hT, hfrac, hnT, m, hm, hfinite, hprime, hpSigma, hpn,
    V, SubalgebraStages.leg S f₀ i.unop,
    SubalgebraStages.isPullback_leg S f₀ i.unop,
    SubalgebraStages.leg_fst S f₀ i.unop, e, ρV, hinj, hsurj, hgraph, hρV⟩



/-- An original finite group action on a generic finite étale cover spreads
with its labels and faithfulness to a finite-residue arithmetic model. -/
theorem exists_arithmetic_cover_action_model_finite_residue
    (K : Type u) [Field K] [CharZero K] [Field.FG K]
    (S₀ : Subalgebra ℤ K) (hS₀ : S₀.FG)
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of S₀)) [QuasiCompact f₀] [QuasiSeparated f₀]
    (W : FiniteEtale (Limits.pullback f₀
      (Spec.map (CommRingCat.ofHom (algebraMap S₀ K)))))
    {G : Type v} [Group G] [Finite G] (ρ : G →* Aut W)
    (n : ℕ) (hn : n ≠ 0) (Sigma : Finset ℕ) :
    ∃ T : Subalgebra S₀ K, T.FG ∧ IsFractionRing T K ∧ IsUnit (n : T) ∧
      ∃ m : Ideal T, m.IsMaximal ∧ Finite (T ⧸ m) ∧
        (ringChar (T ⧸ m)).Prime ∧ ringChar (T ⧸ m) ∉ Sigma ∧
        ¬ ringChar (T ⧸ m) ∣ n ∧
        ∃ (V : FiniteEtale (Limits.pullback f₀
            (Spec.map (CommRingCat.ofHom (algebraMap S₀ T)))))
          (p : Limits.pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))) ⟶
            Limits.pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ T)))),
          IsPullback p
            (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))))
            (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ T))))
            (Spec.map (CommRingCat.ofHom T.val.toRingHom)) ∧
          p ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ T))) =
            Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))) ∧
          ∃ (e : (FiniteEtale.pullback p).obj V ≅ W) (ρV : G →* Aut V),
            (Function.Injective ρ → Function.Injective ρV) ∧ ∀ g : G,
              (FiniteEtale.pullback p).map (ρV g).asIso.hom ≫ e.hom =
                e.hom ≫ (ρ g).asIso.hom := by
  obtain ⟨T, hT, hfrac, hnT, m, hm, hfinite, hprime, hpSigma, hpn,
    V, p, hp, hpfst, e, ρV, hinj, _, _, hρV⟩ :=
    exists_arithmetic_cover_action_model_finite_residue_with_graph K S₀ hS₀ f₀ W ρ n hn Sigma
  exact ⟨T, hT, hfrac, hnT, m, hm, hfinite, hprime, hpSigma, hpn,
    V, p, hp, hpfst, e, ρV, hinj, hρV⟩

/-- An original finite étale generic cover spreads without changing its
pullback identification, to a finite-type arithmetic model where its chosen
nonzero degree is a unit and the finite residue characteristic avoids a
specified finite set. This applies equally to affine and proper families. -/
theorem exists_arithmetic_cover_model_finite_residue
    (K : Type u) [Field K] [CharZero K] [Field.FG K]
    (S₀ : Subalgebra ℤ K) (hS₀ : S₀.FG)
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of S₀)) [QuasiCompact f₀] [QuasiSeparated f₀]
    (W : FiniteEtale (Limits.pullback f₀
      (Spec.map (CommRingCat.ofHom (algebraMap S₀ K)))))
    (n : ℕ) (hn : n ≠ 0) (Sigma : Finset ℕ) :
    ∃ T : Subalgebra S₀ K, T.FG ∧ IsFractionRing T K ∧ IsUnit (n : T) ∧
      ∃ m : Ideal T, m.IsMaximal ∧ Finite (T ⧸ m) ∧
        (ringChar (T ⧸ m)).Prime ∧ ringChar (T ⧸ m) ∉ Sigma ∧
        ¬ ringChar (T ⧸ m) ∣ n ∧
        ∃ (V : FiniteEtale (Limits.pullback f₀
            (Spec.map (CommRingCat.ofHom (algebraMap S₀ T)))))
          (p : Limits.pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))) ⟶
            Limits.pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ T)))),
          IsPullback p
            (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))))
            (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ T))))
            (Spec.map (CommRingCat.ofHom T.val.toRingHom)) ∧
          p ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ T))) =
            Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))) ∧
          Nonempty ((FiniteEtale.pullback p).obj V ≅ W) := by
  obtain ⟨T, hT, hfrac, hnT, m, hm, hfinite, hprime, hpSigma, hpn,
    V, p, hp, hpfst, e, _, _, _⟩ :=
    exists_arithmetic_cover_action_model_finite_residue K S₀ hS₀ f₀ W
      (1 : PUnit.{1} →* Aut W) n hn Sigma
  exact ⟨T, hT, hfrac, hnT, m, hm, hfinite, hprime, hpSigma, hpn,
    V, p, hp, hpfst, ⟨e⟩⟩


/-- An original finite étale Galois cover spreads with its full labelled
deck group and its actual torsor pairing to a finite-residue arithmetic
model. The graph pairing is proved from the native Galois action, not
assumed separately. Connectedness of the special cover is not asserted. -/
theorem exists_arithmetic_galois_torsor_model_finite_residue
    (K : Type u) [Field K] [CharZero K] [Field.FG K]
    (S₀ : Subalgebra ℤ K) (hS₀ : S₀.FG)
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of S₀)) [QuasiCompact f₀] [QuasiSeparated f₀]
    (W : FiniteEtale (Limits.pullback f₀
      (Spec.map (CommRingCat.ofHom (algebraMap S₀ K)))))
    [ConnectedSpace (Limits.pullback f₀
      (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))) : Scheme.{u})]
    [CategoryTheory.PreGaloisCategory.IsGalois W]
    (n : ℕ) (hn : n ≠ 0) (Sigma : Finset ℕ) :
    ∃ T : Subalgebra S₀ K, T.FG ∧ IsFractionRing T K ∧ IsUnit (n : T) ∧
      ∃ m : Ideal T, m.IsMaximal ∧ Finite (T ⧸ m) ∧
        (ringChar (T ⧸ m)).Prime ∧ ringChar (T ⧸ m) ∉ Sigma ∧
        ¬ ringChar (T ⧸ m) ∣ n ∧
        ∃ (V : FiniteEtale (Limits.pullback f₀
            (Spec.map (CommRingCat.ofHom (algebraMap S₀ T)))))
          (p : Limits.pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))) ⟶
            Limits.pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ T)))),
          IsPullback p
            (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))))
            (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ T))))
            (Spec.map (CommRingCat.ofHom T.val.toRingHom)) ∧
          p ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ T))) =
            Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))) ∧
          ∃ (e : (FiniteEtale.pullback p).obj V ≅ W) (ρV : Aut W →* Aut V),
            Function.Injective ρV ∧ Surjective V.hom ∧
            IsIso (graphFamilyMap (fun g : Aut W => (ρV g).asIso.hom)) ∧ ∀ g : Aut W,
              (FiniteEtale.pullback p).map (ρV g).asIso.hom ≫ e.hom =
                e.hom ≫ g.asIso.hom := by
  have : ConnectedSpace W.left := connectedSpace_left_of_isConnected W
  have hsurj : Surjective W.hom := IsFiniteEtale.surjective
    (show W.left ⟶ Limits.pullback f₀
      (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))) from W.hom)
  have hgraph : IsIso (graphFamilyMap (fun g : Aut W => g.asIso.hom)) := by
    change IsIso (CategoryTheory.PreGaloisCategory.galoisSelfProductMap W)
    exact CategoryTheory.PreGaloisCategory.galoisSelfProductMap_isIso
      (CategoryTheory.GaloisCategory.getFiberFunctor _) W
  obtain ⟨T, hT, hfrac, hnT, m, hm, hfinite, hprime, hpSigma, hpn,
    V, p, hp, hpfst, e, ρV, hinj, hcover, hpair, hρV⟩ :=
    exists_arithmetic_cover_action_model_finite_residue_with_graph K S₀ hS₀ f₀ W
      (MonoidHom.id (Aut W)) n hn Sigma
  exact ⟨T, hT, hfrac, hnT, m, hm, hfinite, hprime, hpSigma, hpn,
    V, p, hp, hpfst, e, ρV, hinj Function.injective_id, hcover hsurj, hpair hgraph, hρV⟩


attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

/-- An original finite étale Galois cover of a finite-presentation scheme
over a finitely generated characteristic-zero field admits a labelled,
surjective arithmetic torsor model with finite residue field. The scheme
model is constructed by finite-presentation descent. This includes affine
curves and retains their original cover, without passing to a proper curve
or its ordinary Jacobian. -/
theorem exists_finitelyGenerated_galois_torsor_model_finite_residue
    (K : Type u) [Field K] [CharZero K] [Field.FG K]
    {X : Scheme.{u}} [ConnectedSpace X] (f : X ⟶ Spec (.of K))
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation f]
    (W : FiniteEtale X) [CategoryTheory.PreGaloisCategory.IsGalois W]
    (n : ℕ) (hn : n ≠ 0) (Sigma : Finset ℕ) :
    ∃ T : Subalgebra ℤ K, T.FG ∧ IsFractionRing T K ∧ IsUnit (n : T) ∧
      ∃ m : Ideal T, m.IsMaximal ∧ Finite (T ⧸ m) ∧
        (ringChar (T ⧸ m)).Prime ∧ ringChar (T ⧸ m) ∉ Sigma ∧
        ¬ ringChar (T ⧸ m) ∣ n ∧
        ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of T)) (p : X ⟶ Y),
          LocallyOfFinitePresentation fY ∧ QuasiCompact fY ∧ QuasiSeparated fY ∧
          IsPullback p f fY (Spec.map (CommRingCat.ofHom T.val.toRingHom)) ∧
          ∃ (V : FiniteEtale Y) (e : (FiniteEtale.pullback p).obj V ≅ W)
            (ρV : Aut W →* Aut V), Function.Injective ρV ∧ Surjective V.hom ∧
            IsIso (graphFamilyMap (fun g : Aut W => (ρV g).asIso.hom)) ∧ ∀ g : Aut W,
              (FiniteEtale.pullback p).map (ρV g).asIso.hom ≫ e.hom =
                e.hom ≫ g.asIso.hom := by
  obtain ⟨S₀, hS₀, _, X₀, f₀, q, hfp, hqc, hqs, hpb⟩ :=
    exists_int_subalgebra_isPullback_of_locallyOfFinitePresentation f ∅
  have : LocallyOfFinitePresentation f₀ := hfp
  have : QuasiCompact f₀ := hqc
  have : QuasiSeparated f₀ := hqs
  let Z := Limits.pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ K)))
  let eX : X ≅ Z := hpb.isoPullback
  let H := FiniteEtale.pullback eX.inv
  let F := FiniteEtale.pullback eX.hom
  let W' : FiniteEtale Z := H.obj W
  let ρ' : Aut W →* Aut W' := H.mapAut W
  have : ConnectedSpace W.left := connectedSpace_left_of_isConnected W
  have : Surjective W.hom :=
    IsFiniteEtale.surjective (show W.left ⟶ X from W.hom)
  have hsW' : Surjective W'.hom := by
    change Surjective (Limits.pullback.snd (show W.left ⟶ X from W.hom) eX.inv)
    infer_instance
  have hgraphW : IsIso (graphFamilyMap (fun g : Aut W => g.asIso.hom)) := by
    change IsIso (CategoryTheory.PreGaloisCategory.galoisSelfProductMap W)
    exact CategoryTheory.PreGaloisCategory.galoisSelfProductMap_isIso
      (CategoryTheory.GaloisCategory.getFiberFunctor _) W
  have hgraphW' : IsIso (graphFamilyMap (fun g : Aut W => (ρ' g).asIso.hom)) := by
    have : IsIso (graphFamilyMap (fun g : Aut W => g.asIso.hom)) := hgraphW
    exact graphFamilyMap_pullback_isIso eX.inv W (MonoidHom.id (Aut W))
  obtain ⟨T, hT, hfrac, hnT, m, hm, hfinite, hprime, hpSigma, hpn,
    V, p₀, hp₀, _, e₀, ρV, _, hcover, hpair, hρV⟩ :=
    exists_arithmetic_cover_action_model_finite_residue_with_graph K S₀ hS₀ f₀ W' ρ' n hn Sigma
  let Y := Limits.pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ T)))
  let fY : Y ⟶ Spec (.of T) :=
    Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ T)))
  let p : X ⟶ Y := eX.hom ≫ p₀
  let P := FiniteEtale.pullback p₀
  let P' := FiniteEtale.pullback p
  let C : P' ≅ P ⋙ F := MorphismProperty.Over.pullbackComp
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤) eX.hom p₀ p rfl
  let B : FiniteEtale.pullback (𝟙 X) ≅ H ⋙ F := MorphismProperty.Over.pullbackComp
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
    eX.hom eX.inv (𝟙 X) eX.hom_inv_id.symm
  let η : H ⋙ F ≅ 𝟭 (FiniteEtale X) := B.symm ≪≫ pullbackIdIso X
  let e : P'.obj V ≅ W := C.app V ≪≫ F.mapIso e₀ ≪≫ η.app W
  have hrec (g : Aut W) : P'.map (ρV g).asIso.hom ≫ e.hom =
      e.hom ≫ g.asIso.hom := by
    have hC : P'.map (ρV g).asIso.hom ≫ C.hom.app V =
        C.hom.app V ≫ F.map (P.map (ρV g).asIso.hom) :=
      C.hom.naturality (ρV g).asIso.hom
    have hη : F.map (H.map g.asIso.hom) ≫ η.hom.app W =
        η.hom.app W ≫ g.asIso.hom := η.hom.naturality g.asIso.hom
    calc
      P'.map (ρV g).asIso.hom ≫ e.hom =
          C.hom.app V ≫ F.map (P.map (ρV g).asIso.hom ≫ e₀.hom) ≫ η.hom.app W := by
        change P'.map (ρV g).asIso.hom ≫
          (C.hom.app V ≫ F.map e₀.hom ≫ η.hom.app W) = _
        rw [F.map_comp, ← Category.assoc (P'.map (ρV g).asIso.hom), hC]
        simp only [Category.assoc]
      _ = C.hom.app V ≫ F.map (e₀.hom ≫ H.map g.asIso.hom) ≫ η.hom.app W := by
        have hρ := hρV g
        change P.map (ρV g).asIso.hom ≫ e₀.hom = e₀.hom ≫ H.map g.asIso.hom at hρ
        rw [hρ]
      _ = e.hom ≫ g.asIso.hom := by
        change C.hom.app V ≫ F.map (e₀.hom ≫ H.map g.asIso.hom) ≫ η.hom.app W =
          (C.hom.app V ≫ F.map e₀.hom ≫ η.hom.app W) ≫ g.asIso.hom
        rw [F.map_comp]
        simp only [Category.assoc, hη]
  have hinj : Function.Injective ρV := by
    intro g h hgh
    apply Aut.ext
    apply Iso.ext
    apply (cancel_epi e.hom).mp
    rw [← hrec g, ← hrec h, hgh]
  have hleft : IsPullback eX.hom f
      (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))))
      (𝟙 (Spec (.of K))) :=
    IsPullback.of_horiz_isIso ⟨hpb.isoPullback_hom_snd.trans (Category.comp_id f).symm⟩
  have hp : IsPullback p f fY (Spec.map (CommRingCat.ofHom T.val.toRingHom)) := by
    simpa only [Category.id_comp] using hleft.paste_horiz hp₀
  let R : Subalgebra ℤ K := T.restrictScalars ℤ
  have : Algebra.FiniteType ℤ S₀ := (Subalgebra.fg_iff_finiteType S₀).mp hS₀
  have : Algebra.FiniteType S₀ T := (Subalgebra.fg_iff_finiteType T).mp hT
  have : Algebra.FiniteType ℤ T := Algebra.FiniteType.trans
    (R := ℤ) (S := S₀) (A := T) inferInstance inferInstance
  have hR : R.FG := (Subalgebra.fg_iff_finiteType R).mpr
    (show Algebra.FiniteType ℤ T from inferInstance)
  exact ⟨R, hR, hfrac, hnT, m, hm, hfinite, hprime, hpSigma, hpn,
    Y, fY, p, (show LocallyOfFinitePresentation fY by dsimp only [fY]; infer_instance),
    (show QuasiCompact fY by dsimp only [fY]; infer_instance),
    (show QuasiSeparated fY by dsimp only [fY]; infer_instance), hp,
    V, e, ρV, hinj, hcover hsW', hpair hgraphW', hrec⟩


/-- A proper smooth geometrically connected curve and an original
geometrically connected Galois cover have a proper smooth arithmetic model
with geometrically connected fibres for both curves. The full labelled
finite étale torsor survives at the chosen finite residue field. The cover's
geometric connectedness is essential: a nontrivial constant-field cover
must first be considered over its full field of constants. -/
theorem exists_finitelyGenerated_properSmooth_connected_galois_torsor_model
    (K : Type u) [Field K] [CharZero K] [Field.FG K]
    {X : Scheme.{u}} [ConnectedSpace X] (f : X ⟶ Spec (.of K))
    [IsProper f] [Smooth f] [GeometricallyConnected f]
    (W : FiniteEtale X) [CategoryTheory.PreGaloisCategory.IsGalois W]
    [GeometricallyConnected (W.hom ≫ f)]
    (n : ℕ) (hn : n ≠ 0) (Sigma : Finset ℕ) :
    ∃ T : Subalgebra ℤ K, T.FG ∧ IsFractionRing T K ∧ IsUnit (n : T) ∧
      ∃ m : Ideal T, m.IsMaximal ∧ Finite (T ⧸ m) ∧
        (ringChar (T ⧸ m)).Prime ∧ ringChar (T ⧸ m) ∉ Sigma ∧
        ¬ ringChar (T ⧸ m) ∣ n ∧
        ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of T)) (p : X ⟶ Y),
          IsProper fY ∧ Smooth fY ∧ GeometricallyConnected fY ∧
          IsPullback p f fY (Spec.map (CommRingCat.ofHom T.val.toRingHom)) ∧
          ∃ (V : FiniteEtale Y) (e : (FiniteEtale.pullback p).obj V ≅ W)
            (ρV : Aut W →* Aut V), Function.Injective ρV ∧ Surjective V.hom ∧
            IsIso (graphFamilyMap (fun g : Aut W => (ρV g).asIso.hom)) ∧
            GeometricallyConnected (V.hom ≫ fY) ∧ ∀ g : Aut W,
              (FiniteEtale.pullback p).map (ρV g).asIso.hom ≫ e.hom =
                e.hom ≫ g.asIso.hom := by
  obtain ⟨S₀, hS₀, _, X₀, f₀, q, hproper, hsmooth, hpb⟩ :=
    exists_int_subalgebra_isPullback_of_proper_smooth f ∅
  have : IsProper f₀ := hproper
  have : Smooth f₀ := hsmooth
  let Z := Limits.pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ K)))
  let eX : X ≅ Z := hpb.isoPullback
  let H := FiniteEtale.pullback eX.inv
  let F := FiniteEtale.pullback eX.hom
  let W' : FiniteEtale Z := H.obj W
  let ρ' : Aut W →* Aut W' := H.mapAut W
  have : ConnectedSpace W.left := connectedSpace_left_of_isConnected W
  have : Surjective W.hom :=
    IsFiniteEtale.surjective (show W.left ⟶ X from W.hom)
  have hsW' : Surjective W'.hom := by
    change Surjective (Limits.pullback.snd (show W.left ⟶ X from W.hom) eX.inv)
    infer_instance
  have hgraphW : IsIso (graphFamilyMap (fun g : Aut W => g.asIso.hom)) := by
    change IsIso (CategoryTheory.PreGaloisCategory.galoisSelfProductMap W)
    exact CategoryTheory.PreGaloisCategory.galoisSelfProductMap_isIso
      (CategoryTheory.GaloisCategory.getFiberFunctor _) W
  have hgraphW' : IsIso (graphFamilyMap (fun g : Aut W => (ρ' g).asIso.hom)) := by
    have : IsIso (graphFamilyMap (fun g : Aut W => g.asIso.hom)) := hgraphW
    exact graphFamilyMap_pullback_isIso eX.inv W (MonoidHom.id (Aut W))
  obtain ⟨T, hT, hfrac, hnT, m, hm, hfinite, hprime, hpSigma, hpn,
    V, p₀, hp₀, _, e₀, ρV, _, hcover, hpair, hρV⟩ :=
    exists_arithmetic_cover_action_model_finite_residue_with_graph K S₀ hS₀ f₀ W' ρ' n hn Sigma
  let Y := Limits.pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ T)))
  let fY : Y ⟶ Spec (.of T) :=
    Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ T)))
  let p : X ⟶ Y := eX.hom ≫ p₀
  let P := FiniteEtale.pullback p₀
  let P' := FiniteEtale.pullback p
  let C : P' ≅ P ⋙ F := MorphismProperty.Over.pullbackComp
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤) eX.hom p₀ p rfl
  let B : FiniteEtale.pullback (𝟙 X) ≅ H ⋙ F := MorphismProperty.Over.pullbackComp
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
    eX.hom eX.inv (𝟙 X) eX.hom_inv_id.symm
  let η : H ⋙ F ≅ 𝟭 (FiniteEtale X) := B.symm ≪≫ pullbackIdIso X
  let e : P'.obj V ≅ W := C.app V ≪≫ F.mapIso e₀ ≪≫ η.app W
  have hrec (g : Aut W) : P'.map (ρV g).asIso.hom ≫ e.hom =
      e.hom ≫ g.asIso.hom := by
    have hC : P'.map (ρV g).asIso.hom ≫ C.hom.app V =
        C.hom.app V ≫ F.map (P.map (ρV g).asIso.hom) :=
      C.hom.naturality (ρV g).asIso.hom
    have hη : F.map (H.map g.asIso.hom) ≫ η.hom.app W =
        η.hom.app W ≫ g.asIso.hom := η.hom.naturality g.asIso.hom
    calc
      P'.map (ρV g).asIso.hom ≫ e.hom =
          C.hom.app V ≫ F.map (P.map (ρV g).asIso.hom ≫ e₀.hom) ≫ η.hom.app W := by
        change P'.map (ρV g).asIso.hom ≫
          (C.hom.app V ≫ F.map e₀.hom ≫ η.hom.app W) = _
        rw [F.map_comp, ← Category.assoc (P'.map (ρV g).asIso.hom), hC]
        simp only [Category.assoc]
      _ = C.hom.app V ≫ F.map (e₀.hom ≫ H.map g.asIso.hom) ≫ η.hom.app W := by
        have hρ := hρV g
        change P.map (ρV g).asIso.hom ≫ e₀.hom = e₀.hom ≫ H.map g.asIso.hom at hρ
        rw [hρ]
      _ = e.hom ≫ g.asIso.hom := by
        change C.hom.app V ≫ F.map (e₀.hom ≫ H.map g.asIso.hom) ≫ η.hom.app W =
          (C.hom.app V ≫ F.map e₀.hom ≫ η.hom.app W) ≫ g.asIso.hom
        rw [F.map_comp]
        simp only [Category.assoc, hη]
  have hinj : Function.Injective ρV := by
    intro g h hgh
    apply Aut.ext
    apply Iso.ext
    apply (cancel_epi e.hom).mp
    rw [← hrec g, ← hrec h, hgh]
  have hleft : IsPullback eX.hom f
      (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))))
      (𝟙 (Spec (.of K))) :=
    IsPullback.of_horiz_isIso ⟨hpb.isoPullback_hom_snd.trans (Category.comp_id f).symm⟩
  have hp : IsPullback p f fY (Spec.map (CommRingCat.ofHom T.val.toRingHom)) := by
    simpa only [Category.id_comp] using hleft.paste_horiz hp₀
  let R : Subalgebra ℤ K := T.restrictScalars ℤ
  have : Algebra.FiniteType ℤ S₀ := (Subalgebra.fg_iff_finiteType S₀).mp hS₀
  have : Algebra.FiniteType S₀ T := (Subalgebra.fg_iff_finiteType T).mp hT
  have : Algebra.FiniteType ℤ T := Algebra.FiniteType.trans
    (R := ℤ) (S := S₀) (A := T) inferInstance inferInstance
  have hR : R.FG := (Subalgebra.fg_iff_finiteType R).mpr
    (show Algebra.FiniteType ℤ T from inferInstance)
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing ℤ T
  have hproperY : IsProper fY := by dsimp only [fY]; infer_instance
  have hsmoothY : Smooth fY := by dsimp only [fY]; infer_instance
  have hgcBase : GeometricallyConnected fY := by
    have : MorphismProperty.RespectsIso
        (@GeometricallyConnected : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have : GeometricallyConnected
        (Limits.pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap T K)))) :=
      (GeomConnDesc.iff_of_isPullback (P := @GeometricallyConnected.{u}) hp).mpr inferInstance
    exact GeometricallyConnected.of_injective_coefficient_baseChange
      (R := T) (A := K) Subtype.val_injective fY
  have : IsIso e.inv.left := by
    change IsIso ((FiniteEtale.forget X ⋙ CategoryTheory.Over.forget X).map e.inv)
    infer_instance
  have hleftCover : IsPullback e.inv.left W.hom ((FiniteEtale.pullback p).obj V).hom
      (𝟙 X) := IsPullback.of_horiz_isIso
    (snd := (show W.left ⟶ X from W.hom))
    (f := (show ((FiniteEtale.pullback p).obj V).left ⟶ X from
      ((FiniteEtale.pullback p).obj V).hom)) (g := (𝟙 X : X ⟶ X))
    ⟨(MorphismProperty.Over.w e.inv).trans (Category.comp_id W.hom).symm⟩
  have hcoverSquare : IsPullback
      (e.inv.left ≫ Limits.pullback.fst V.hom p) W.hom V.hom p := by
    have h := hleftCover.paste_horiz
      (IsPullback.of_hasPullback (show V.left ⟶ Y from V.hom) p)
    exact (congrArg (fun r : X ⟶ Y =>
      IsPullback (e.inv.left ≫ Limits.pullback.fst V.hom p)
        (show W.left ⟶ X from W.hom) (show V.left ⟶ Y from V.hom) r)
      (Category.id_comp p)).mp h
  have htotalSquare := hcoverSquare.paste_vert hp
  have hgcCover : GeometricallyConnected (V.hom ≫ fY) := by
    have : MorphismProperty.RespectsIso
        (@GeometricallyConnected : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have : GeometricallyConnected (Limits.pullback.snd (V.hom ≫ fY)
        (Spec.map (CommRingCat.ofHom (algebraMap T K)))) :=
      (GeomConnDesc.iff_of_isPullback (P := @GeometricallyConnected.{u})
        htotalSquare).mpr inferInstance
    exact GeometricallyConnected.of_injective_coefficient_baseChange
      (R := T) (A := K) Subtype.val_injective (V.hom ≫ fY)
  exact ⟨R, hR, hfrac, hnT, m, hm, hfinite, hprime, hpSigma, hpn,
    Y, fY, p, hproperY, hsmoothY, hgcBase, hp,
    V, e, ρV, hinj, hcover hsW', hpair hgraphW', hgcCover, hrec⟩

private theorem refine_coefficient_square
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of A)} {f₀ : Y ⟶ Spec (.of R)}
    {q : X ⟶ Y}
    (sq : IsPullback q f f₀ (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    (T : Subalgebra R A) :
    ∃ r : X ⟶ Limits.pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap R T))),
      r ≫ Limits.pullback.fst f₀ _ = q ∧
      IsPullback r f (Limits.pullback.snd f₀ _)
        (Spec.map (CommRingCat.ofHom (algebraMap T A))) := by
  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap T A)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R T)) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let r := Limits.pullback.lift q
    (f ≫ Spec.map (CommRingCat.ofHom (algebraMap T A)))
    (by rw [Category.assoc, hcomp]; exact sq.w)
  refine ⟨r, Limits.pullback.lift_fst _ _ _, ?_⟩
  refine IsPullback.of_right (h₁₂ := Limits.pullback.fst f₀ _)
    (v₁₃ := f₀) (h₂₂ := Spec.map (CommRingCat.ofHom (algebraMap R T)))
    ?_ (Limits.pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f₀ _)
  rw [Limits.pullback.lift_fst, hcomp]
  exact sq

/-- Compare a closed immersion with its map between two fixed Cartesian models.
Keeping the six schemes explicit avoids unfolding the coefficient-stage constructions. -/
private theorem isClosedImmersion_of_cartesian_comparison
    {C D C₀ D₀ S S₀ : Scheme.{u}}
    (i : D ⟶ C) [IsClosedImmersion i]
    (c : C ⟶ S) (d : D ⟶ S) (c₀ : C₀ ⟶ S₀) (d₀ : D₀ ⟶ S₀)
    (pC : C ⟶ C₀) (pD : D ⟶ D₀) (b : S ⟶ S₀)
    (sqC : IsPullback pC c c₀ b) (sqD : IsPullback pD d d₀ b)
    (i₀ : D₀ ⟶ C₀) (hi : i ≫ c = d) (hrec : pD ≫ i₀ = i ≫ pC)
    (iK : Limits.pullback d₀ b ⟶ Limits.pullback c₀ b)
    (hfst : iK ≫ Limits.pullback.fst c₀ b = Limits.pullback.fst d₀ b ≫ i₀)
    (hsnd : iK ≫ Limits.pullback.snd c₀ b = Limits.pullback.snd d₀ b) :
    IsClosedImmersion iK := by
  have hcomparison : sqD.isoPullback.hom ≫ iK = i ≫ sqC.isoPullback.hom := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hfst, ← Category.assoc,
        sqD.isoPullback_hom_fst, Category.assoc, sqC.isoPullback_hom_fst, hrec]
    · rw [Category.assoc, hsnd, sqD.isoPullback_hom_snd,
        Category.assoc, sqC.isoPullback_hom_snd, hi]
  have hiK : iK = sqD.isoPullback.inv ≫ i ≫ sqC.isoPullback.hom := by
    rw [← hcomparison, Iso.inv_hom_id_assoc]
  rw [hiK]
  infer_instance

/-- Refining both models by the same base change preserves the original
compatible map. The proof only uses the two projections of each pullback. -/
private theorem compatible_map_after_baseChange
    {C D C₀ D₀ S S₀ S₁ : Scheme.{u}}
    (i : D ⟶ C) (c : C ⟶ S) (d : D ⟶ S)
    (c₀ : C₀ ⟶ S₀) (d₀ : D₀ ⟶ S₀)
    (pC : C ⟶ C₀) (pD : D ⟶ D₀) (u : S₁ ⟶ S₀) (b : S ⟶ S₁)
    (rC : C ⟶ Limits.pullback c₀ u) (rD : D ⟶ Limits.pullback d₀ u)
    (hCfst : rC ≫ Limits.pullback.fst c₀ u = pC)
    (hDfst : rD ≫ Limits.pullback.fst d₀ u = pD)
    (sqC : IsPullback rC c (Limits.pullback.snd c₀ u) b)
    (sqD : IsPullback rD d (Limits.pullback.snd d₀ u) b)
    (i₀ : D₀ ⟶ C₀) (hi : i ≫ c = d) (hrec : pD ≫ i₀ = i ≫ pC)
    (i₁ : Limits.pullback d₀ u ⟶ Limits.pullback c₀ u)
    (hfst : i₁ ≫ Limits.pullback.fst c₀ u = Limits.pullback.fst d₀ u ≫ i₀)
    (hsnd : i₁ ≫ Limits.pullback.snd c₀ u = Limits.pullback.snd d₀ u) :
    rD ≫ i₁ = i ≫ rC := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, hfst, ← Category.assoc, hDfst,
      Category.assoc, hCfst, hrec]
  · rw [Category.assoc, hsnd, sqD.w, Category.assoc,
      sqC.w, ← Category.assoc i, hi]

/-- Descend the original closed boundary from two fixed Cartesian models.
The coefficient ring is kept abstract while the compatible map and its
closed-immersion property descend through the final coefficient enlargements. -/
private theorem exists_pair_model_of_cartesian_models
    (K : Type u) [Field K]
    (R₁ : Type u) [CommRing R₁] [Algebra R₁ K] [Algebra.FiniteType ℤ R₁]
    {C C₁ : Scheme.{u}} (f : C ⟶ Spec (.of K))
    (D : FiniteEtale (Spec (.of K)))
    (i : D.left ⟶ C) [IsClosedImmersion i] (hi : i ≫ f = D.hom)
    (c₁ : C₁ ⟶ Spec (.of R₁)) [IsProper c₁] [Smooth c₁]
    (D₁ : FiniteEtale (Spec (.of R₁)))
    (pC₁ : C ⟶ C₁) (pD₁ : D.left ⟶ D₁.left)
    (sqC₁ : IsPullback pC₁ f c₁
      (Spec.map (CommRingCat.ofHom (algebraMap R₁ K))))
    (sqD₁ : IsPullback pD₁ D.hom D₁.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R₁ K)))) :
    ∃ R : Subalgebra ℤ K, R.FG ∧
      ∃ (C₀ : Scheme.{u}) (f₀ : C₀ ⟶ Spec (.of R))
        (D₀ : FiniteEtale (Spec (.of R))) (i₀ : D₀.left ⟶ C₀)
        (pC : C ⟶ C₀) (pD : D.left ⟶ D₀.left),
        IsProper f₀ ∧ Smooth f₀ ∧ IsClosedImmersion i₀ ∧ i₀ ≫ f₀ = D₀.hom ∧
        IsPullback pC f f₀ (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
        IsPullback pD D.hom D₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
        pD ≫ i₀ = i ≫ pC := by
  classical
  let d : D.left ⟶ Spec (.of K) := D.hom
  let d₁ : D₁.left ⟶ Spec (.of R₁) := D₁.hom
  have : IsFiniteEtale d₁ := D₁.prop
  let g := sqD₁.isoPullback.inv ≫ i ≫ sqC₁.isoPullback.hom
  have hg : g ≫ Limits.pullback.snd c₁ _ = Limits.pullback.snd d₁ _ := by
    change (sqD₁.isoPullback.inv ≫ i ≫ sqC₁.isoPullback.hom) ≫ _ = _
    rw [Category.assoc, Category.assoc, sqC₁.isoPullback_hom_snd]
    exact (congrArg (sqD₁.isoPullback.inv ≫ ·) hi).trans sqD₁.isoPullback_inv_snd
  obtain ⟨T, hT, _, m, hm, hrec⟩ :=
    exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (A₀ := R₁) (A := K) d₁ c₁ g hg ∅
  let c₂ := Limits.pullback.snd c₁
    (Spec.map (CommRingCat.ofHom (R := R₁) (S := T) (algebraMap R₁ T)))
  let d₂ := Limits.pullback.snd d₁
    (Spec.map (CommRingCat.ofHom (R := R₁) (S := T) (algebraMap R₁ T)))
  have : IsProper c₂ := inferInstance
  have : Smooth c₂ := inferInstance
  obtain ⟨pC₂, hpC₂, sqC₂⟩ := refine_coefficient_square sqC₁ T
  obtain ⟨pD₂, hpD₂, sqD₂⟩ := refine_coefficient_square sqD₁ T
  have hrec₂ : pD₂ ≫ m = i ≫ pC₂ := by
    let qD := sqD₁.isoPullback.inv ≫ pD₂
    let qC := sqC₁.isoPullback.inv ≫ pC₂
    have hqDfst : qD ≫ Limits.pullback.fst d₁ _ =
        Limits.pullback.fst d₁ _ := by
      dsimp only [qD]
      rw [Category.assoc, hpD₂, sqD₁.isoPullback_inv_fst]
    have hqDbase : qD ≫ d₂ = Limits.pullback.snd d₁ _ ≫
        Spec.map (CommRingCat.ofHom T.val.toRingHom) := by
      have hbase : pD₂ ≫ d₂ =
          d ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) := sqD₂.w
      dsimp only [qD]
      rw [Category.assoc, hbase, ← Category.assoc, sqD₁.isoPullback_inv_snd]
    have hqCfst : qC ≫ Limits.pullback.fst c₁ _ = Limits.pullback.fst c₁ _ := by
      dsimp only [qC]
      rw [Category.assoc, hpC₂, sqC₁.isoPullback_inv_fst]
    have hqCbase : qC ≫ c₂ = Limits.pullback.snd c₁ _ ≫
        Spec.map (CommRingCat.ofHom T.val.toRingHom) := by
      have hbase : pC₂ ≫ c₂ =
          f ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) := sqC₂.w
      dsimp only [qC]
      rw [Category.assoc, hbase, ← Category.assoc, sqC₁.isoPullback_inv_snd]
    have H := hrec qD qC hqDfst hqDbase hqCfst hqCbase
    apply (cancel_epi sqD₁.isoPullback.inv).mp
    simpa only [qD, qC, g, Category.assoc, Iso.hom_inv_id_assoc] using H
  have : IsFinite (m ≫ c₂) := hm.symm ▸ (inferInstanceAs (IsFinite d₂))
  have : Etale (m ≫ c₂) := hm.symm ▸ (inferInstanceAs (Etale d₂))
  have : QuasiCompact (m ≫ c₂) := hm.symm ▸ (inferInstanceAs (QuasiCompact d₂))
  have : QuasiSeparated (m ≫ c₂) := hm.symm ▸ (inferInstanceAs (QuasiSeparated d₂))
  have : LocallyOfFiniteType (m ≫ c₂) :=
    hm.symm ▸ (inferInstanceAs (LocallyOfFiniteType d₂))
  have : QuasiCompact m := QuasiCompact.of_comp m c₂
  have : QuasiSeparated m := QuasiSeparated.of_comp m c₂
  have : LocallyOfFiniteType m := locallyOfFiniteType_of_comp m c₂
  have sqD₂' : IsPullback pD₂ d (m ≫ c₂)
      (Spec.map (CommRingCat.ofHom (algebraMap T K))) := by
    rw [hm]
    exact sqD₂
  have hclosed (mK : Limits.pullback (m ≫ c₂)
        (Spec.map (CommRingCat.ofHom (algebraMap T K))) ⟶
        Limits.pullback c₂ (Spec.map (CommRingCat.ofHom (algebraMap T K))))
      (hfst : mK ≫ Limits.pullback.fst c₂ _ = Limits.pullback.fst (m ≫ c₂) _ ≫ m)
      (hsnd : mK ≫ Limits.pullback.snd c₂ _ = Limits.pullback.snd (m ≫ c₂) _) :
      IsClosedImmersion mK := by
    exact isClosedImmersion_of_cartesian_comparison i f d c₂ (m ≫ c₂)
      pC₂ pD₂ (Spec.map (CommRingCat.ofHom (algebraMap T K)))
      sqC₂ sqD₂' m hi hrec₂ mK hfst hsnd
  obtain ⟨U, hU, _, hUclosed⟩ :=
    IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact
      (A₀ := T) (A := K) m c₂ hclosed ∅
  let : CommRing U := Subalgebra.toCommRing (R := T) (A := K) U
  let c₃ := Limits.pullback.snd c₂
    (Spec.map (CommRingCat.ofHom (R := T) (S := U) (algebraMap T U)))
  let d₃ := Limits.pullback.snd (m ≫ c₂)
    (Spec.map (CommRingCat.ofHom (R := T) (S := U) (algebraMap T U)))
  let u : Spec (.of U) ⟶ Spec (.of T) :=
    Spec.map (CommRingCat.ofHom (R := T) (S := U) (algebraMap T U))
  let i₃ : Limits.pullback (m ≫ c₂) u ⟶ Limits.pullback c₂ u :=
    Limits.pullback.lift (Limits.pullback.fst (m ≫ c₂) u ≫ m)
      (Limits.pullback.snd (m ≫ c₂) u)
      ((Category.assoc (Limits.pullback.fst (m ≫ c₂) u) m c₂).trans
        (Limits.pullback.condition (f := m ≫ c₂) (g := u)))
  have hi₃fst : i₃ ≫ Limits.pullback.fst c₂ _ =
      Limits.pullback.fst (m ≫ c₂) _ ≫ m := Limits.pullback.lift_fst _ _ _
  have hi₃base : i₃ ≫ c₃ = d₃ := Limits.pullback.lift_snd _ _ _
  have : IsClosedImmersion i₃ := hUclosed i₃ hi₃fst hi₃base
  have hD₃ : IsFiniteEtale d₃ := @IsFiniteEtale.mk _ _ _ inferInstance inferInstance
  obtain ⟨pC₃, hpC₃, sqC₃⟩ := refine_coefficient_square sqC₂ U
  obtain ⟨pD₃, hpD₃, sqD₃⟩ := refine_coefficient_square sqD₂' U
  have hrec₃ : pD₃ ≫ i₃ = i ≫ pC₃ := by
    exact compatible_map_after_baseChange i f d c₂ (m ≫ c₂) pC₂ pD₂ u
      (Spec.map (CommRingCat.ofHom (algebraMap U K))) pC₃ pD₃
      hpC₃ hpD₃ sqC₃ sqD₃ m hi hrec₂ i₃ hi₃fst hi₃base
  have : Algebra.FiniteType R₁ T := (Subalgebra.fg_iff_finiteType _).mp hT
  have : Algebra.FiniteType ℤ T := Algebra.FiniteType.trans (S := R₁) inferInstance inferInstance
  have : Algebra.FiniteType T U := (Subalgebra.fg_iff_finiteType _).mp hU
  have : Algebra.FiniteType ℤ U := Algebra.FiniteType.trans (S := T) inferInstance inferInstance
  let R : Subalgebra ℤ K := U.restrictScalars ℤ
  have hR : R.FG := (Subalgebra.fg_iff_finiteType R).mpr
    (show Algebra.FiniteType ℤ U from inferInstance)
  exact ⟨R, hR, _, c₃, @FiniteEtale.mk (Spec (.of U)) _ d₃ hD₃, i₃, pC₃, pD₃,
    (show IsProper c₃ from inferInstance), (show Smooth c₃ from inferInstance),
    (show IsClosedImmersion i₃ from inferInstance), hi₃base, sqC₃, sqD₃, hrec₃⟩


/-- A proper smooth scheme together with an actual finite étale closed
boundary descends to a common finite-type integer algebra. Both Cartesian
squares and the original boundary inclusion are retained. -/
theorem exists_properSmooth_finiteEtale_pair_model
    (K : Type u) [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K))
    [IsProper f] [Smooth f] (D : FiniteEtale (Spec (.of K)))
    (i : D.left ⟶ C) [IsClosedImmersion i] (hi : i ≫ f = D.hom) :
    ∃ R : Subalgebra ℤ K, R.FG ∧
      ∃ (C₀ : Scheme.{u}) (f₀ : C₀ ⟶ Spec (.of R))
        (D₀ : FiniteEtale (Spec (.of R))) (i₀ : D₀.left ⟶ C₀)
        (pC : C ⟶ C₀) (pD : D.left ⟶ D₀.left),
        IsProper f₀ ∧ Smooth f₀ ∧ IsClosedImmersion i₀ ∧ i₀ ≫ f₀ = D₀.hom ∧
        IsPullback pC f f₀ (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
        IsPullback pD D.hom D₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
        pD ≫ i₀ = i ≫ pC := by
  classical
  let d : D.left ⟶ Spec (.of K) := D.hom
  obtain ⟨R₀, hR₀, _, C₀, f₀, p₀, hproper₀, hsmooth₀, sqC₀⟩ :=
    exists_int_subalgebra_isPullback_of_proper_smooth f ∅
  have : IsProper f₀ := hproper₀
  have : Smooth f₀ := hsmooth₀
  let S : Finset K →o Subalgebra R₀ K :=
    { toFun := fun s => Algebra.adjoin R₀ (s : Set K)
      monotone' := fun _ _ h => Algebra.adjoin_mono h }
  have hS (x : K) : ∃ s : Finset K, x ∈ S s :=
    ⟨{x}, Algebra.subset_adjoin (Finset.mem_singleton_self x)⟩
  obtain ⟨hlim⟩ :=
    (open AlgebraicCurves.Geometry.Schemes.Proofs.SubalgebraStages_nonempty_isLimit_cone in
      LimBC.nonempty_isLimit_specCone S hS)
  have {a b : (Finset K)ᵒᵖ} (h : a ⟶ b) :
      IsAffineHom ((SubalgebraStages.specDiagram S).map h) :=
    isAffineHom_of_isAffine _
  have (a : (Finset K)ᵒᵖ) : CompactSpace ((SubalgebraStages.specDiagram S).obj a) := by
    change CompactSpace (Spec (.of (S a.unop)))
    infer_instance
  have (a : (Finset K)ᵒᵖ) : QuasiSeparatedSpace ((SubalgebraStages.specDiagram S).obj a) := by
    change QuasiSeparatedSpace (Spec (.of (S a.unop)))
    infer_instance
  obtain ⟨a, D₁, ⟨eD⟩⟩ := exists_inverse_limit_model
    (SubalgebraStages.specDiagram S) (SubalgebraStages.specCone S) hlim D
  let R₁ := S a.unop
  let d₁ : D₁.left ⟶ Spec (.of R₁) := D₁.hom
  have : IsFiniteEtale d₁ := D₁.prop
  have hR₁ : R₁.FG := Subalgebra.fg_adjoin_finset a.unop
  let c₁ := Limits.pullback.snd f₀
    (Spec.map (CommRingCat.ofHom (algebraMap R₀ R₁)))
  obtain ⟨pC₁, _hpC₁, sqC₁⟩ := refine_coefficient_square sqC₀ R₁
  have : IsProper c₁ := inferInstance
  have : Smooth c₁ := inferInstance
  have : IsIso eD.inv.left := by
    change IsIso ((FiniteEtale.forget (Spec (.of K)) ⋙
      CategoryTheory.Over.forget (Spec (.of K))).map eD.inv)
    infer_instance
  have sqDleft : IsPullback eD.inv.left d
      ((FiniteEtale.pullback (Spec.map (CommRingCat.ofHom (algebraMap R₁ K)))).obj D₁).hom
      (𝟙 (Spec (.of K))) := by
    exact @IsPullback.of_horiz_isIso Scheme.{u} Scheme.instCategory _ _ _ _ _ _ _ _
      (inferInstanceAs (IsIso eD.inv.left)) (IsIso.id (Spec (.of K)))
      ⟨(MorphismProperty.Over.w eD.inv).trans (Category.comp_id d).symm⟩
  let pD₁ : D.left ⟶ D₁.left := eD.inv.left ≫ Limits.pullback.fst d₁
    (Spec.map (CommRingCat.ofHom (algebraMap R₁ K)))
  have sqD₁ : IsPullback pD₁ d d₁
      (Spec.map (CommRingCat.ofHom (algebraMap R₁ K))) := by
    have h := sqDleft.paste_horiz (IsPullback.of_hasPullback d₁
      (Spec.map (CommRingCat.ofHom (algebraMap R₁ K))))
    exact (congrArg (fun r : Spec (.of K) ⟶ Spec (.of R₁) =>
      IsPullback pD₁ d d₁ r)
      (Category.id_comp (Spec.map (CommRingCat.ofHom (algebraMap R₁ K))))).mp h
  have hFiniteType₀ : Algebra.FiniteType ℤ R₀ :=
    (Subalgebra.fg_iff_finiteType _).mp hR₀
  have hFiniteType₁₀ : Algebra.FiniteType R₀ R₁ :=
    (Subalgebra.fg_iff_finiteType _).mp hR₁
  have hFiniteType₁ : Algebra.FiniteType ℤ R₁ :=
    Algebra.FiniteType.trans (S := R₀) hFiniteType₀ hFiniteType₁₀
  exact exists_pair_model_of_cartesian_models K R₁ f D i hi c₁ D₁
    pC₁ pD₁ sqC₁ sqD₁

/-- The original smooth curve is the Cartesian generic fibre of the exact
open complement of a finite étale boundary in a proper smooth arithmetic
scheme. No boundary component is discarded. -/
theorem exists_original_curve_open_pair_model
    (K : Type u) [Field K] [PerfectField K]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f] :
    ∃ R : Subalgebra ℤ K, R.FG ∧
      ∃ (C₀ : Scheme.{u}) (c₀ : C₀ ⟶ Spec (.of R))
        (D₀ : FiniteEtale (Spec (.of R))) (i₀ : D₀.left ⟶ C₀)
        (U₀ : C₀.Opens) (p : X ⟶ U₀),
        IsProper c₀ ∧ Smooth c₀ ∧ IsClosedImmersion i₀ ∧ i₀ ≫ c₀ = D₀.hom ∧
        (U₀ : Set C₀) = (Set.range i₀)ᶜ ∧
        IsPullback p f (U₀.ι ≫ c₀)
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  let : Algebra K X.functionField := (AlgebraicCurve.baseToFunctionField f).toAlgebra
  obtain ⟨M, j, B, b, hj, hjbase, hb, hbfin, hbet, hboundary, _hgeneric⟩ :=
    AlgebraicCurve.exists_curveModel_finiteEtale_boundary_of_smooth_curve K f
  have : IsOpenImmersion j := hj
  have : IsClosedImmersion b := hb
  have : IsFinite (b ≫ M.toBase) := hbfin
  have : Etale (b ≫ M.toBase) := hbet
  have : IsFiniteEtale (b ≫ M.toBase) := @IsFiniteEtale.mk _ _ _ hbfin hbet
  have : IsProper M.toBase := M.isProper
  have : SmoothOfRelativeDimension 1 M.toBase := M.smooth
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  let D := FiniteEtale.mk (b ≫ M.toBase)
  have : IsClosedImmersion (show D.left ⟶ M.C from b) := hb
  obtain ⟨R, hR, C₀, c₀, D₀, i₀, pC, pD,
    hcproper, hcsmooth, hi₀, hi₀base, sqC, sqD, hpair⟩ :=
    exists_properSmooth_finiteEtale_pair_model K M.toBase D b rfl
  have : IsProper c₀ := hcproper
  have : Smooth c₀ := hcsmooth
  have : IsClosedImmersion i₀ := hi₀
  have sqPair : IsPullback pD b i₀ pC := by
    apply IsPullback.of_bot (v₂₁ := M.toBase) (v₂₂ := c₀)
      (h₃₁ := Spec.map (CommRingCat.ofHom (algebraMap R K))) _ hpair sqC
    rw [hi₀base]
    exact sqD
  have hpreBoundary : Set.range b = pC ⁻¹' Set.range i₀ := by
    calc
      Set.range b = Set.range (Limits.pullback.snd i₀ pC) := by
        rw [← sqPair.isoPullback_hom_snd]
        exact sqPair.isoPullback.hom.surjective.range_comp _
      _ = pC ⁻¹' Set.range i₀ := Scheme.Pullback.range_snd i₀ pC
  let U₀ : C₀.Opens :=
    ⟨(Set.range i₀)ᶜ, i₀.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hpre : pC ⁻¹ᵁ U₀ = j.opensRange := by
    apply TopologicalSpace.Opens.ext
    change (pC ⁻¹' Set.range i₀)ᶜ = Set.range j
    rw [← hpreBoundary, hboundary, compl_compl]
  have hrange : Set.range (j ≫ pC) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : j x ∈ pC ⁻¹ᵁ U₀ := by
      rw [hpre]
      exact Set.mem_range_self x
    exact hx
  let p := IsOpenImmersion.lift U₀.ι (j ≫ pC) hrange
  have hp : p ≫ U₀.ι = j ≫ pC := IsOpenImmersion.lift_fac _ _ _
  have sqOpen : IsPullback p j U₀.ι pC :=
    IsOpenImmersion.isPullback p j U₀.ι pC hp.symm
      (by rw [Scheme.Opens.opensRange_ι]; exact hpre)
  have sq : IsPullback p f (U₀.ι ≫ c₀)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    rw [← hjbase]
    exact sqOpen.paste_vert sqC
  exact ⟨R, hR, C₀, c₀, D₀, i₀, U₀, p,
    hcproper, hcsmooth, hi₀, hi₀base, rfl, sq⟩

/-- A chosen finite Galois cover of the original smooth curve descends with
its labelled deck action to the base change of a constructed proper smooth
pair with finite étale boundary. The arithmetic coefficient field remains
exactly the original field, and the closed residue characteristic avoids
the prescribed finite set and the given nonzero degree. -/
theorem exists_finitelyGenerated_curve_pair_galois_torsor_model
    (K : Type u) [Field K] [CharZero K] [Field.FG K]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
    (W : FiniteEtale X) [CategoryTheory.PreGaloisCategory.IsGalois W]
    (n : ℕ) (hn : n ≠ 0) (Sigma : Finset ℕ) :
    ∃ (R : Subalgebra ℤ K), R.FG ∧
      ∃ (C₀ : Scheme.{u}) (c₀ : C₀ ⟶ Spec (.of R))
        (D₀ : FiniteEtale (Spec (.of R))) (i₀ : D₀.left ⟶ C₀)
        (U₀ : C₀.Opens),
        IsProper c₀ ∧ Smooth c₀ ∧ IsClosedImmersion i₀ ∧ i₀ ≫ c₀ = D₀.hom ∧
        (U₀ : Set C₀) = (Set.range i₀)ᶜ ∧
        ∃ T : Subalgebra R K, T.FG ∧ IsFractionRing T K ∧ IsUnit (n : T) ∧
          ∃ m : Ideal T, m.IsMaximal ∧ Finite (T ⧸ m) ∧
            (ringChar (T ⧸ m)).Prime ∧ ringChar (T ⧸ m) ∉ Sigma ∧
            ¬ ringChar (T ⧸ m) ∣ n ∧
            ∃ (V : FiniteEtale (Limits.pullback (U₀.ι ≫ c₀)
                (Spec.map (CommRingCat.ofHom (algebraMap R T)))))
              (p : X ⟶ Limits.pullback (U₀.ι ≫ c₀)
                (Spec.map (CommRingCat.ofHom (algebraMap R T)))),
              IsPullback p f (Limits.pullback.snd (U₀.ι ≫ c₀)
                (Spec.map (CommRingCat.ofHom (algebraMap R T))))
                (Spec.map (CommRingCat.ofHom (algebraMap T K))) ∧
              ∃ (e : (FiniteEtale.pullback p).obj V ≅ W) (ρV : Aut W →* Aut V),
                Function.Injective ρV ∧ Surjective V.hom ∧
                IsIso (graphFamilyMap (fun g : Aut W => (ρV g).asIso.hom)) ∧
                ∀ g : Aut W, (FiniteEtale.pullback p).map (ρV g).asIso.hom ≫ e.hom =
                  e.hom ≫ g.asIso.hom := by
  obtain ⟨R, hR, C₀, c₀, D₀, i₀, U₀, q, hcproper, hcsmooth,
    hi₀, hi₀base, hcomplement, hpb⟩ := exists_original_curve_open_pair_model K f
  have : IsProper c₀ := hcproper
  have : Smooth c₀ := hcsmooth
  have : Algebra.FiniteType ℤ R := (Subalgebra.fg_iff_finiteType _).mp hR
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have : IsLocallyNoetherian C₀ := LocallyOfFiniteType.isLocallyNoetherian c₀
  have : CompactSpace C₀ := QuasiCompact.compactSpace_of_compactSpace c₀
  have : IsNoetherian C₀ := ⟨⟩
  let f₀ := U₀.ι ≫ c₀
  have : QuasiCompact f₀ := inferInstance
  have : QuasiSeparated f₀ := inferInstance
  let Z := Limits.pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  let eX : X ≅ Z := hpb.isoPullback
  let H := FiniteEtale.pullback eX.inv
  let F := FiniteEtale.pullback eX.hom
  let W' : FiniteEtale Z := H.obj W
  let ρ' : Aut W →* Aut W' := H.mapAut W
  have : ConnectedSpace W.left := connectedSpace_left_of_isConnected W
  have : Surjective W.hom :=
    IsFiniteEtale.surjective (show W.left ⟶ X from W.hom)
  have hsW' : Surjective W'.hom := by
    change Surjective (Limits.pullback.snd (show W.left ⟶ X from W.hom) eX.inv)
    infer_instance
  have hgraphW : IsIso (graphFamilyMap (fun g : Aut W => g.asIso.hom)) := by
    change IsIso (CategoryTheory.PreGaloisCategory.galoisSelfProductMap W)
    exact CategoryTheory.PreGaloisCategory.galoisSelfProductMap_isIso
      (CategoryTheory.GaloisCategory.getFiberFunctor _) W
  have hgraphW' : IsIso (graphFamilyMap (fun g : Aut W => (ρ' g).asIso.hom)) := by
    have : IsIso (graphFamilyMap (fun g : Aut W => g.asIso.hom)) := hgraphW
    exact graphFamilyMap_pullback_isIso eX.inv W (MonoidHom.id (Aut W))
  obtain ⟨T, hT, hfrac, hnT, m, hm, hfinite, hprime, hpSigma, hpn,
    V, p₀, hp₀, _, e₀, ρV, _, hcover, hpair, hρV⟩ :=
    exists_arithmetic_cover_action_model_finite_residue_with_graph K R hR f₀ W' ρ' n hn Sigma
  let p := eX.hom ≫ p₀
  let P := FiniteEtale.pullback p₀
  let P' := FiniteEtale.pullback p
  let E : P' ≅ P ⋙ F := MorphismProperty.Over.pullbackComp
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤) eX.hom p₀ p rfl
  let B : FiniteEtale.pullback (𝟙 X) ≅ H ⋙ F := MorphismProperty.Over.pullbackComp
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
    eX.hom eX.inv (𝟙 X) eX.hom_inv_id.symm
  let η : H ⋙ F ≅ 𝟭 (FiniteEtale X) := B.symm ≪≫ pullbackIdIso X
  let e : P'.obj V ≅ W := E.app V ≪≫ F.mapIso e₀ ≪≫ η.app W
  have hrec (g : Aut W) : P'.map (ρV g).asIso.hom ≫ e.hom = e.hom ≫ g.asIso.hom := by
    have hE : P'.map (ρV g).asIso.hom ≫ E.hom.app V =
        E.hom.app V ≫ F.map (P.map (ρV g).asIso.hom) := E.hom.naturality (ρV g).asIso.hom
    have hη : F.map (H.map g.asIso.hom) ≫ η.hom.app W =
        η.hom.app W ≫ g.asIso.hom := η.hom.naturality g.asIso.hom
    calc
      P'.map (ρV g).asIso.hom ≫ e.hom =
          E.hom.app V ≫ F.map (P.map (ρV g).asIso.hom ≫ e₀.hom) ≫ η.hom.app W := by
        change P'.map (ρV g).asIso.hom ≫
          (E.hom.app V ≫ F.map e₀.hom ≫ η.hom.app W) = _
        rw [F.map_comp, ← Category.assoc (P'.map (ρV g).asIso.hom), hE]
        simp only [Category.assoc]
      _ = E.hom.app V ≫ F.map (e₀.hom ≫ H.map g.asIso.hom) ≫ η.hom.app W := by
        have hg := hρV g
        change P.map (ρV g).asIso.hom ≫ e₀.hom =
          e₀.hom ≫ H.map g.asIso.hom at hg
        rw [hg]
      _ = e.hom ≫ g.asIso.hom := by
        change E.hom.app V ≫ F.map (e₀.hom ≫ H.map g.asIso.hom) ≫ η.hom.app W =
          (E.hom.app V ≫ F.map e₀.hom ≫ η.hom.app W) ≫ g.asIso.hom
        rw [F.map_comp]
        simp only [Category.assoc, hη]
  have hinj : Function.Injective ρV := by
    intro g h hgh
    apply Aut.ext
    apply Iso.ext
    apply (cancel_epi e.hom).mp
    rw [← hrec g, ← hrec h, hgh]
  have hleft : IsPullback eX.hom f
      (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (𝟙 (Spec (.of K))) :=
    IsPullback.of_horiz_isIso ⟨hpb.isoPullback_hom_snd.trans (Category.comp_id f).symm⟩
  have hp : IsPullback p f (Limits.pullback.snd f₀
      (Spec.map (CommRingCat.ofHom (algebraMap R T))))
      (Spec.map (CommRingCat.ofHom (algebraMap T K))) := by
    have h := hleft.paste_horiz hp₀
    change IsPullback p f (Limits.pullback.snd f₀
      (Spec.map (CommRingCat.ofHom (algebraMap R T))))
      (𝟙 (Spec (.of K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap T K))) at h
    rw [Category.id_comp] at h
    exact h
  exact ⟨R, hR, C₀, c₀, D₀, i₀, U₀, hcproper, hcsmooth,
    hi₀, hi₀base, hcomplement, T, hT, hfrac, hnT, m, hm, hfinite, hprime, hpSigma, hpn,
    V, p, hp, e, ρV, hinj, hcover hsW', hpair hgraphW', hrec⟩

/-- The original smooth curve and a chosen Galois cover admit a smooth,
normal arithmetic model inside the same function field. The compactification
and its finite étale boundary are retained by the displayed coefficient base
change, as are every original deck label and the invertible torsor graph.
The prescribed degree is invertible and the chosen closed residue avoids the
specified characteristics. This constructs the arithmetic model, without
asserting an affine étale or tame specialization comparison. -/
theorem exists_finitelyGenerated_normal_curve_pair_galois_torsor_model
    (K : Type u) [Field K] [CharZero K] [Field.FG K]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
    (W : FiniteEtale X) [CategoryTheory.PreGaloisCategory.IsGalois W]
    (n : ℕ) (hn : n ≠ 0) (Sigma : Finset ℕ) :
    ∃ (R : Subalgebra ℤ K), R.FG ∧
      ∃ (C₀ : Scheme.{u}) (c₀ : C₀ ⟶ Spec (.of R))
        (D₀ : FiniteEtale (Spec (.of R))) (i₀ : D₀.left ⟶ C₀)
        (U₀ : C₀.Opens),
        IsProper c₀ ∧ Smooth c₀ ∧ IsClosedImmersion i₀ ∧ i₀ ≫ c₀ = D₀.hom ∧
        (U₀ : Set C₀) = (Set.range i₀)ᶜ ∧
        ∃ (B : Subalgebra ℤ K) (hRB : R ≤ B),
          B.FG ∧ Algebra.Smooth ℤ B ∧ IsIntegrallyClosed B ∧
          IsFractionRing B K ∧ IsUnit (n : B) ∧
          ∃ m : Ideal B, m.IsMaximal ∧ Finite (B ⧸ m) ∧
            (ringChar (B ⧸ m)).Prime ∧ ringChar (B ⧸ m) ∉ Sigma ∧
            ¬ ringChar (B ⧸ m) ∣ n ∧
            ∃ (V : FiniteEtale (Limits.pullback (U₀.ι ≫ c₀)
                (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRB).toRingHom))))
              (p : X ⟶ Limits.pullback (U₀.ι ≫ c₀)
                (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRB).toRingHom))),
              IsPullback p f (Limits.pullback.snd (U₀.ι ≫ c₀)
                (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRB).toRingHom)))
                (Spec.map (CommRingCat.ofHom (algebraMap B K))) ∧
              ∃ (e : (FiniteEtale.pullback p).obj V ≅ W) (ρV : Aut W →* Aut V),
                Function.Injective ρV ∧ Surjective V.hom ∧
                IsIso (graphFamilyMap (fun g : Aut W => (ρV g).asIso.hom)) ∧
                ∀ g : Aut W, (FiniteEtale.pullback p).map (ρV g).asIso.hom ≫ e.hom =
                  e.hom ≫ g.asIso.hom := by
  classical
  let primes := Sigma.filter Nat.Prime
  let aux := primes.prod id
  have haux : aux ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun q hq =>
    (Finset.mem_filter.mp hq).2.ne_zero)
  let ell := n * aux
  have hell : ell ≠ 0 := Nat.mul_ne_zero hn haux
  obtain ⟨R, hR, C₀, c₀, D₀, i₀, U₀, hcproper, hcsmooth,
      hi₀, hi₀base, hcomplement, T, hT, hfrac, hellT,
      _, _, _, _, _, _, V, p₀, hp₀, e₀, ρV, _, hcover, hgraph, hρV⟩ :=
    exists_finitelyGenerated_curve_pair_galois_torsor_model K f W ell hell ∅
  have : Algebra.FiniteType ℤ R := (Subalgebra.fg_iff_finiteType R).mp hR
  have : Algebra.FiniteType R T := (Subalgebra.fg_iff_finiteType T).mp hT
  have : Algebra.FiniteType ℤ T := Algebra.FiniteType.trans
    (R := ℤ) (S := R) (A := T) inferInstance inferInstance
  let S : Subalgebra ℤ K := T.restrictScalars ℤ
  have hS : S.FG := (Subalgebra.fg_iff_finiteType S).mpr
    (show Algebra.FiniteType ℤ T from inferInstance)
  have : IsFractionRing S K := hfrac
  obtain ⟨B, hSB, hB, hsmB, hnormalB, hfracB⟩ :=
    Subalgebra.exists_le_normal_int_model_of_fg S hS
  have hRS : R ≤ S := fun x hx => T.algebraMap_mem ⟨x, hx⟩
  let hRB : R ≤ B := hRS.trans hSB
  let iTB : T →+* B := (Subalgebra.inclusion hSB).toRingHom
  have hellB : IsUnit (ell : B) := by
    simpa only [map_natCast] using hellT.map iTB
  have hnB : IsUnit (n : B) := isUnit_of_mul_isUnit_left
    (show IsUnit ((n : B) * (aux : B)) from
      by simpa only [ell, Nat.cast_mul] using hellB)
  let f₀ := U₀.ι ≫ c₀
  let a₀ := Spec.map (CommRingCat.ofHom (algebraMap R T))
  let a := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRB).toRingHom)
  let b : Spec (.of B) ⟶ Spec (.of T) := Spec.map (CommRingCat.ofHom iTB)
  let t := Spec.map (CommRingCat.ofHom (algebraMap T K))
  let s := Spec.map (CommRingCat.ofHom (algebraMap B K))
  have hba : b ≫ a₀ = a := by
    rw [← Spec.map_comp]
    rfl
  have hsb : s ≫ b = t := by
    rw [← Spec.map_comp]
    rfl
  let q : Limits.pullback f₀ a ⟶ Limits.pullback f₀ a₀ :=
    Limits.pullback.lift (Limits.pullback.fst f₀ a)
      (Limits.pullback.snd f₀ a ≫ b)
      (by rw [Category.assoc, hba]; exact Limits.pullback.condition)
  have hqfst : q ≫ Limits.pullback.fst f₀ a₀ = Limits.pullback.fst f₀ a :=
    Limits.pullback.lift_fst _ _ _
  have hqsnd : q ≫ Limits.pullback.snd f₀ a₀ = Limits.pullback.snd f₀ a ≫ b :=
    Limits.pullback.lift_snd _ _ _
  have houter : IsPullback (p₀ ≫ Limits.pullback.fst f₀ a₀) f f₀ (t ≫ a₀) :=
    hp₀.paste_horiz (IsPullback.of_hasPullback f₀ a₀)
  have hsa : s ≫ a = t ≫ a₀ := by rw [← hba, ← Category.assoc, hsb]
  let p : X ⟶ Limits.pullback f₀ a :=
    Limits.pullback.lift (p₀ ≫ Limits.pullback.fst f₀ a₀) (f ≫ s)
      (houter.w.trans ((congrArg (f ≫ ·) hsa.symm).trans
        (Category.assoc f s a).symm))
  have hpfst : p ≫ Limits.pullback.fst f₀ a = p₀ ≫ Limits.pullback.fst f₀ a₀ :=
    Limits.pullback.lift_fst _ _ _
  have hpsnd : p ≫ Limits.pullback.snd f₀ a = f ≫ s :=
    Limits.pullback.lift_snd _ _ _
  have hp : IsPullback p f (Limits.pullback.snd f₀ a) s := by
    apply IsPullback.of_right (h₁₂ := Limits.pullback.fst f₀ a)
      (v₁₃ := f₀) (h₂₂ := a) ?_ hpsnd (IsPullback.of_hasPullback f₀ a)
    rw [hpfst, hsa]
    exact houter
  have hpq : p ≫ q = p₀ := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hqfst, hpfst]
    · rw [Category.assoc, hqsnd, ← Category.assoc, hpsnd, Category.assoc, hsb]
      exact hp₀.w.symm
  let F := FiniteEtale.pullback q
  let V' := F.obj V
  let ρ' : Aut W →* Aut V' := (F.mapAut V).comp ρV
  let E : FiniteEtale.pullback p₀ ≅ F ⋙ FiniteEtale.pullback p :=
    MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤) p q p₀ hpq.symm
  let e : (FiniteEtale.pullback p).obj V' ≅ W := (E.symm.app V) ≪≫ e₀
  have hrec (g : Aut W) :
      (FiniteEtale.pullback p).map (ρ' g).asIso.hom ≫ e.hom =
        e.hom ≫ g.asIso.hom := by
    change (FiniteEtale.pullback p).map (F.map (ρV g).asIso.hom) ≫
        (E.inv.app V ≫ e₀.hom) = (E.inv.app V ≫ e₀.hom) ≫ g.asIso.hom
    have hE : (FiniteEtale.pullback p).map (F.map (ρV g).asIso.hom) ≫ E.inv.app V =
        E.inv.app V ≫ (FiniteEtale.pullback p₀).map (ρV g).asIso.hom :=
      E.inv.naturality (ρV g).asIso.hom
    rw [← Category.assoc, hE, Category.assoc, hρV g, Category.assoc]
  have hinj : Function.Injective ρ' := by
    intro g h hgh
    apply Aut.ext
    apply Iso.ext
    apply (cancel_epi e.hom).mp
    rw [← hrec g, ← hrec h, hgh]
  have : Surjective V.hom := hcover
  have hcover' : Surjective V'.hom := by
    change Surjective (Limits.pullback.snd
      (show V.left ⟶ Limits.pullback f₀ a₀ from V.hom) q)
    infer_instance
  have : IsIso (graphFamilyMap (fun g : Aut W => (ρV g).asIso.hom)) := hgraph
  have hgraph' : IsIso (graphFamilyMap (fun g : Aut W => (ρ' g).asIso.hom)) :=
    graphFamilyMap_pullback_isIso q V ρV
  have : Algebra.FiniteType ℤ B := (Subalgebra.fg_iff_finiteType B).mp hB
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  have : m.IsMaximal := hm
  let _ : Field (B ⧸ m) := Ideal.Quotient.field m
  have hfinite : Finite (B ⧸ m) := FieldTheory.finite_quotient_of_finiteType_int B m
  have : Algebra.FiniteType ℤ (B ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mk m).toIntAlgHom
      Ideal.Quotient.mk_surjective
  have hchar : ringChar (B ⧸ m) ≠ 0 := FieldTheory.ringChar_ne_zero_of_finiteType_int (B ⧸ m)
  have hprime : (ringChar (B ⧸ m)).Prime :=
    (CharP.char_is_prime_or_zero (B ⧸ m) (ringChar (B ⧸ m))).resolve_right hchar
  have hnotdvd : ¬ ringChar (B ⧸ m) ∣ ell := by
    intro hdvd
    have hu : IsUnit (ell : B ⧸ m) := by
      simpa only [map_natCast] using hellB.map (Ideal.Quotient.mk m)
    exact hu.ne_zero ((CharP.cast_eq_zero_iff (B ⧸ m) (ringChar (B ⧸ m)) ell).mpr hdvd)
  have hpSigma : ringChar (B ⧸ m) ∉ Sigma := by
    intro hpSigma
    exact hnotdvd (dvd_mul_of_dvd_right
      (Finset.dvd_prod_of_mem id (Finset.mem_filter.mpr ⟨hpSigma, hprime⟩)) n)
  have hpn : ¬ ringChar (B ⧸ m) ∣ n := fun h =>
    hnotdvd (dvd_mul_of_dvd_left h aux)
  exact ⟨R, hR, C₀, c₀, D₀, i₀, U₀, hcproper, hcsmooth,
    hi₀, hi₀base, hcomplement, B, hRB, hB, hsmB, hnormalB, hfracB, hnB,
    m, hm, hfinite, hprime, hpSigma, hpn, V', p, hp, e, ρ', hinj, hcover', hgraph', hrec⟩

end AlgebraicGeometry.FiniteEtale
