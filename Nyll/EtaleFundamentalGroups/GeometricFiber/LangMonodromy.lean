/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.LangTranslations
public import Nyll.EtaleFundamentalGroups.Cohomology.TorsorCharacter
public import Mathlib.CategoryTheory.Galois.Topology
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Native monodromy of Lang pullbacks

The actual finite étale fiber is identified with the fiber of the Lang
homomorphism on geometric points. Its kernel acts by the original deck
translations. Naturality therefore makes native geometric monodromy a
translation, whose displacement descends to the topological abelianization.
No connected component of the covering is selected.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.PreGaloisCategory

namespace GoodReductionJacobian.RelativeGroupLaw.LangMonodromy

/-- A point of a pullback satisfies its defining square after projection. -/
theorem pullback_point_fst {X Y Z T : Scheme} (u : X ⟶ Z) (v : Y ⟶ Z)
    (w : T ⟶ pullback u v) (y : T ⟶ Y) (hy : w ≫ pullback.snd u v = y) :
    (w ≫ pullback.fst u v) ≫ u = y ≫ v :=
  (Category.assoc _ _ _).trans
    ((congrArg (w ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ v) hy)))

private theorem point_commuting_square {X Y T : Scheme}
    (w : T ⟶ X) (d : X ⟶ X) (u : X ⟶ Y) (e : Y ⟶ Y)
    (h : d ≫ u = u ≫ e) : (w ≫ d) ≫ u = (w ≫ u) ≫ e :=
  (Category.assoc _ _ _).trans
    ((congrArg (w ≫ ·) h).trans (Category.assoc _ _ _).symm)

/-- A nonempty fiber of a group homomorphism is a torsor under its kernel. -/
@[instance_reducible]
def homFiberTorsor {S T P : Type*} [Group S] [Group T]
    (φ : S →* T) (t : T) (e : P ≃ {x : S // φ x = t}) (hn : Nonempty P) :
    Torsor φ.ker P := by
  let act (s : φ.ker) (z : P) : P := e.symm
    ⟨s.val * (e z).val, (map_mul φ _ _).trans
      ((congrArg (· * φ (e z).val) s.property).trans
        ((_root_.one_mul _).trans (e z).property))⟩
  let diff (x y : P) : φ.ker := ⟨(e x).val / (e y).val,
    (map_div φ _ _).trans
      ((congrArg₂ (· / ·) (e x).property (e y).property).trans (div_self' t))⟩
  have hact (s : φ.ker) (z : P) : (e (act s z)).val = s.val * (e z).val :=
    congrArg Subtype.val (e.apply_symm_apply _)
  exact
    { smul := act
      sdiv := diff
      nonempty := hn
      one_smul z := by
        exact e.injective (Subtype.ext ((hact 1 z).trans (_root_.one_mul _)))
      mul_smul s r z := by
        apply e.injective
        apply Subtype.ext
        exact (hact (s * r) z).trans
          ((_root_.mul_assoc s.val r.val (e z).val).trans
            ((congrArg (s.val * ·) (hact r z).symm).trans (hact s (act r z)).symm))
      sdiv_smul' x y := by
        exact e.injective
          (Subtype.ext ((hact (diff x y) y).trans (div_mul_cancel _ _)))
      smul_sdiv' s z := by
        apply Subtype.ext
        exact (congrArg (· / (e z).val) (hact s z)).trans (mul_div_cancel_right _ _) }

private theorem homFiberTorsor_smul
    {S T P : Type*} [Group S] [Group T]
    (φ : S →* T) (t : T) (e : P ≃ {x : S // φ x = t}) (hn : Nonempty P)
    (s : φ.ker) (z : P) :
    let _ : Torsor φ.ker P := homFiberTorsor φ t e hn
    (e (s • z)).val = s.val * (e z).val := by
  exact congrArg Subtype.val (e.apply_symm_apply _)

private theorem homFiberTorsor_sdiv
    {S T P : Type*} [Group S] [Group T]
    (φ : S →* T) (t : T) (e : P ≃ {x : S // φ x = t}) (hn : Nonempty P)
    (x y : P) :
    let _ : Torsor φ.ker P := homFiberTorsor φ t e hn
    (x /ₛ y : φ.ker).val = (e x).val / (e y).val := rfl

variable (k : Type) [Field k] [Fintype k]
  (A : Scheme) [A.Over (Spec (CommRingCat.of k))]
  (G : RelativeGroupLaw k (A ↘ Spec (CommRingCat.of k))) (hc : G.IsCommutative)
  (Ω : Type) [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]

local notation "f" => (A ↘ Spec (CommRingCat.of k))
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k Ω))
local notation "g" => pullback.snd f b
local notation "λΩ" => finiteFieldLangMap k Ω A G hc

/-- Rational geometric sections, retaining the given group law in the carrier
so its point-group instance is determined without an extra choice. -/
def Points : Type :=
  (fun (_L : RelativeGroupLaw k f) (_hL : _L.IsCommutative) =>
    SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω))) g) G hc

instance : CommGroup (Points k A G hc Ω) :=
  (G.baseChange b).pointCommGroup (hc.baseChange b) (𝟙 _)

local notation "S" => Points k A G hc Ω

/-- The actual geometric Lang morphism evaluated on rational sections. -/
def pointHom : S →* S :=
  MonoidHom.mk' (fun x : S => (NeronModelInfra.schemeHomOverComp x λΩ : S))
    (finiteFieldLangMap_mul k A G hc Ω (𝟙 _))

/-- The kernel consists of actual sections of the geometric Lang morphism. -/
def Kernel := (pointHom k A G hc Ω).ker

instance : CommGroup (Kernel k A G hc Ω) :=
  inferInstanceAs (CommGroup (pointHom k A G hc Ω).ker)

instance : TopologicalSpace (Kernel k A G hc Ω) := ⊥

instance : DiscreteTopology (Kernel k A G hc Ω) := ⟨rfl⟩

variable [IsAlgClosed Ω]
  (hA : AbelianSchemePropertyBundle k (A ↘ Spec (CommRingCat.of k)))
  {C : Scheme} (c : C ⟶ Spec (CommRingCat.of Ω))
  (a : SchemeHomOver c (pullback.snd (A ↘ Spec (CommRingCat.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))
  (xi : SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω))) c)

local notation "V" =>
  Functor.obj (FiniteEtale.pullback (Subtype.val a)) (geometricLangCover k A G hc Ω hA)
local notation "F" => FiniteEtale.fiber (Subtype.val xi)
local notation "P" => ObjectProperty.FullSubcategory.obj (Functor.obj F V : FintypeCat)
local notation "target" => NeronModelInfra.schemeHomOverComp xi a

/-- The original geometric group-scheme point underlying a native fiber point. -/
def coordinate (z : P) : S := by
  let w : Over.mk xi.val ⟶ (V).toComma := FiniteEtale.fiberObjEquivHom xi.val V z
  have hw : (w.left ≫ pullback.fst (λΩ).val a.val) ≫ (λΩ).val =
      xi.val ≫ a.val :=
    pullback_point_fst (λΩ).val a.val w.left xi.val (Over.w w)
  refine ⟨w.left ≫ pullback.fst (λΩ).val a.val, ?_⟩
  calc
    (w.left ≫ pullback.fst (λΩ).val a.val) ≫ g =
        ((w.left ≫ pullback.fst (λΩ).val a.val) ≫ (λΩ).val) ≫ g :=
      (congrArg (fun r => (w.left ≫ pullback.fst (λΩ).val a.val) ≫ r)
        (λΩ).property).symm.trans (Category.assoc _ _ _).symm
    _ = (xi.val ≫ a.val) ≫ g := congrArg (· ≫ g) hw
    _ = 𝟙 _ := (Category.assoc _ _ _).trans
      ((congrArg (xi.val ≫ ·) a.property).trans xi.property)

/-- The coordinate lies over the original image of the selected base point. -/
theorem pointHom_coordinate (z : P) :
    pointHom k A G hc Ω (coordinate k A G hc Ω hA c a xi z) = target := by
  apply Subtype.ext
  let w : Over.mk xi.val ⟶ (V).toComma := FiniteEtale.fiberObjEquivHom xi.val V z
  change (w.left ≫ pullback.fst (λΩ).val a.val) ≫ (λΩ).val = xi.val ≫ a.val
  exact pullback_point_fst (λΩ).val a.val w.left xi.val (Over.w w)

/-- Native finite étale fiber points are exactly the original Lang solutions. -/
def fiberEquiv : P ≃ {z : S // pointHom k A G hc Ω z = target} where
  toFun z := ⟨coordinate k A G hc Ω hA c a xi z,
    pointHom_coordinate k A G hc Ω hA c a xi z⟩
  invFun z := (FiniteEtale.fiberObjEquivHom xi.val V).symm
    (Over.homMk (pullback.lift z.val.val xi.val (congrArg Subtype.val z.property))
      (pullback.lift_snd _ _ _))
  left_inv z := by
    apply (FiniteEtale.fiberObjEquivHom xi.val V).injective
    change (FiniteEtale.fiberObjEquivHom xi.val V)
      ((FiniteEtale.fiberObjEquivHom xi.val V).symm _) = _
    rw [Equiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans
        (Over.w (FiniteEtale.fiberObjEquivHom xi.val V z)).symm
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    change (FiniteEtale.fiberObjEquivHom xi.val V
      ((FiniteEtale.fiberObjEquivHom xi.val V).symm _)).left ≫
        pullback.fst (λΩ).val a.val = z.val.val
    rw [Equiv.apply_symm_apply]
    exact pullback.lift_fst _ _ _

/-- The inverse fiber comparison retains the prescribed original coordinate. -/
theorem coordinate_fiberEquiv_symm (z : {z : S // pointHom k A G hc Ω z = target}) :
    coordinate k A G hc Ω hA c a xi ((fiberEquiv k A G hc Ω hA c a xi).symm z) =
      z.val :=
  congrArg Subtype.val ((fiberEquiv k A G hc Ω hA c a xi).apply_symm_apply z)

/-- Coordinates distinguish native fiber points. -/
theorem coordinate_injective : Function.Injective (coordinate k A G hc Ω hA c a xi) := by
  intro x y h
  exact (fiberEquiv k A G hc Ω hA c a xi).injective (Subtype.ext h)

/-- Lang surjectivity supplies a point of every native fiber, without
requiring connectedness of its pulled-back finite étale cover. -/
theorem fiber_nonempty : Nonempty P := by
  obtain ⟨z, hz⟩ := surjective_finiteFieldLangMap_points k Ω A G hc hA target
  exact ⟨(fiberEquiv k A G hc Ω hA c a xi).symm ⟨z, hz⟩⟩

/-- The action of a native deck translation is multiplication by its actual
kernel point in the geometric group scheme. -/
theorem coordinate_map_translation (t : Kernel k A G hc Ω) (z : P) :
    coordinate k A G hc Ω hA c a xi
        ((F).map
          (geometricLangPullbackTranslation k A G hc Ω hA a.val t.val t.property).asIso.hom z) =
      t.val * coordinate k A G hc Ω hA c a xi z := by
  let d := geometricLangPullbackTranslation k A G hc Ω hA a.val t.val t.property
  let w : Over.mk xi.val ⟶ (V).toComma := FiniteEtale.fiberObjEquivHom xi.val V z
  have hw := congrArg (fun r : Over.mk xi.val ⟶ (V).toComma => r.left)
    (FiniteEtale.fiberObjEquivHom_naturality xi.val d.asIso.hom z).symm
  have hw' : (FiniteEtale.fiberObjEquivHom xi.val V ((F).map d.asIso.hom z)).left =
      w.left ≫ d.asIso.hom.left := hw
  have ht : GoodReductionJacobian.schemeHomOverComp (𝟙 (Spec (CommRingCat.of Ω)))
      (Category.comp_id _) t.val = t.val := Subtype.ext (Category.id_comp _)
  apply Subtype.ext
  change (FiniteEtale.fiberObjEquivHom xi.val V ((F).map d.asIso.hom z)).left ≫
      pullback.fst (λΩ).val a.val =
    ((G.baseChange b).mul (𝟙 _) t.val (coordinate k A G hc Ω hA c a xi z)).val
  exact (congrArg (· ≫ pullback.fst (λΩ).val a.val) hw').trans
    ((point_commuting_square w.left d.asIso.hom.left (pullback.fst (λΩ).val a.val)
      ((G.baseChange b).translate t.val)
      (geometricLangPullbackTranslation_fst k A G hc Ω hA a.val t.val t.property)).trans
        (((G.baseChange b).point_comp_translate (𝟙 _)
          (coordinate k A G hc Ω hA c a xi z) t.val).trans
          ((congrArg (fun u => ((G.baseChange b).mul (𝟙 _)
            (coordinate k A G hc Ω hA c a xi z) u).val) ht).trans
              (congrArg Subtype.val ((hc.baseChange b) _ _ _)))))

/-- The torsor structure is on the original native fiber, with original
kernel sections as its coefficient group. Lang surjectivity supplies nonemptiness. -/
@[instance_reducible]
def fiberTorsor : Torsor (Kernel k A G hc Ω) P :=
  homFiberTorsor (pointHom k A G hc Ω) (target : S)
    (fiberEquiv k A G hc Ω hA c a xi) (fiber_nonempty k A G hc Ω hA c a xi)

local instance : Torsor (Kernel k A G hc Ω) P := fiberTorsor k A G hc Ω hA c a xi

include hA c a xi in
/-- The actual Lang kernel is finite, by its free action on the native finite fiber. -/
theorem kernel_finite : Finite (Kernel k A G hc Ω) := by
  let p : P := Classical.choice (fiber_nonempty k A G hc Ω hA c a xi)
  exact Finite.of_injective (fun t : Kernel k A G hc Ω => t • p)
    (fun _ _ h => smul_right_cancel p h)

/-- Torsor translation is exactly the original deck automorphism on the native fiber. -/
theorem smul_eq_map_translation (t : Kernel k A G hc Ω) (z : P) :
    t • z = (F).map
      (geometricLangPullbackTranslation k A G hc Ω hA a.val t.val t.property).asIso.hom z := by
  apply coordinate_injective k A G hc Ω hA c a xi
  exact (homFiberTorsor_smul (pointHom k A G hc Ω) (target : S)
    (fiberEquiv k A G hc Ω hA c a xi) (fiber_nonempty k A G hc Ω hA c a xi)
    t z).trans (coordinate_map_translation k A G hc Ω hA c a xi t z).symm

/-- The original geometric monodromy commutes with these actual kernel translations. -/
instance : SMulCommClass π₁ᵉᵗ(xi.val) (Kernel k A G hc Ω) P where
  smul_comm γ t z := by
    rw [smul_eq_map_translation, smul_eq_map_translation]
    exact geometricLangPullbackTranslation_monodromy k A G hc Ω hA a.val xi.val
      t.val t.property γ z

variable [ConnectedSpace C]

/-- The continuous displacement character of the original native Lang action. -/
def character (p : P) : π₁ᵉᵗ(xi.val) →ₜ* Kernel k A G hc Ω :=
  EtaleFundamentalGroups.Cohomology.torsorCharacter
    (G := π₁ᵉᵗ(xi.val)) (A := Kernel k A G hc Ω) («P» := P) p

/-- Actual geometric Lang monodromy descends through the closed-commutator quotient. -/
def abelianCharacter (p : P) :
    TopologicalAbelianization π₁ᵉᵗ(xi.val) →ₜ* Kernel k A G hc Ω :=
  ProCGroups.Abelian.TopologicalAbelianization.lift (character k A G hc Ω hA c a xi p)

omit [ConnectedSpace C] in
/-- Its value is the ratio of the two original geometric group-scheme coordinates. -/
theorem abelianCharacter_apply_mk (p : P) (γ : π₁ᵉᵗ(xi.val)) :
    (abelianCharacter k A G hc Ω hA c a xi p
      (ProCGroups.Abelian.TopologicalAbelianization.mk π₁ᵉᵗ(xi.val) γ)).val =
    coordinate k A G hc Ω hA c a xi (γ • p) /
      coordinate k A G hc Ω hA c a xi p := by
  exact (congrArg Subtype.val
    (ProCGroups.Abelian.TopologicalAbelianization.lift_apply_mk
      (character k A G hc Ω hA c a xi p) γ)).trans
    (homFiberTorsor_sdiv (pointHom k A G hc Ω) (target : S)
      (fiberEquiv k A G hc Ω hA c a xi) (fiber_nonempty k A G hc Ω hA c a xi)
      (γ • p) p)

omit [ConnectedSpace C] in
/-- The descended character recovers the original monodromy on every point,
not just on the chosen point used to present the torsor. -/
theorem abelianCharacter_smul (p : P) (γ : π₁ᵉᵗ(xi.val)) (z : P) :
    abelianCharacter k A G hc Ω hA c a xi p
        (ProCGroups.Abelian.TopologicalAbelianization.mk π₁ᵉᵗ(xi.val) γ) • z = γ • z := by
  rw [show abelianCharacter k A G hc Ω hA c a xi p
      (ProCGroups.Abelian.TopologicalAbelianization.mk π₁ᵉᵗ(xi.val) γ) =
      (γ • p) /ₛ p from
    ProCGroups.Abelian.TopologicalAbelianization.lift_apply_mk
      (character k A G hc Ω hA c a xi p) γ]
  have h := congrArg (fun χ : π₁ᵉᵗ(xi.val) →ₜ* Kernel k A G hc Ω => χ γ)
    (EtaleFundamentalGroups.Cohomology.torsorCharacter_eq
      (G := π₁ᵉᵗ(xi.val)) (A := Kernel k A G hc Ω) («P» := P) p z)
  exact (congrArg (· • z) h).trans (sdiv_smul (γ • z) z)

end GoodReductionJacobian.RelativeGroupLaw.LangMonodromy
