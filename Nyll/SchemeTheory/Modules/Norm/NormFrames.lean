/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_dual_eq_of_ihomEval_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isFrameOn_dual.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_basis_smul_pushforward.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isFrameOn_normModule.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Nyll.SchemeTheory.Modules.Sections.IhomSections
import Nyll.SchemeTheory.Modules.ExteriorPower.Det
import Nyll.SchemeTheory.Modules.Norm.NormModule
import Nyll.SchemeTheory.Modules.Frames.IsFrameOnSheafificationAdjunctionUnitIotaMulti
import Nyll.SchemeTheory.Modules.Tensor.TensorFrames

/-!
# Scheme Modules Is Frame On dual eq of ihom Eval eq
-/

section IsFrameOn_dual_eq_of_ihomEval_eq

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_dual_eq_of_ihomEval_eq

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.Opposite


lemma presheaf_map_map_aux {X : Scheme.{u}} (M : X.Modules) {A B C : X.Opens} (f : B ⟶ A) (g : C ⟶
  B) (k : C ⟶ A)
    (x : Γ(M, A)) : M.presheaf.map g.op (M.presheaf.map f.op x) = M.presheaf.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (g ≫ f) k]

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.dual_eq_of_ihomEval_eq
    {X : Scheme.{u}} {P : X.Modules} {U V : X.Opens} {p : Γ(P, U)}
    (hp : Scheme.Modules.IsFrameOn p V) (hVU : V ≤ U) {q q' : Γ(Scheme.Modules.dual P, V)}
    (h : Scheme.Modules.ihomEval P (𝟙_ X.Modules) V (P.presheaf.map (homOfLE hVU).op p) q =
      Scheme.Modules.ihomEval P (𝟙_ X.Modules) V (P.presheaf.map (homOfLE hVU).op p) q') :
    q = q' := by
  apply Scheme.Modules.ihom_sections_ext
  intro W i m
  obtain ⟨c, hc⟩ := (hp (i.le.trans hVU) i.le).2 m
  change c • P.presheaf.map (homOfLE (i.le.trans hVU)).op p = m at hc
  have hres : P.presheaf.map (homOfLE (i.le.trans hVU)).op p = P.presheaf.map i.op (P.presheaf.map
    (homOfLE hVU).op p) :=
    (presheaf_map_map_aux P _ _ _ p).symm
  rw [← hc, hres, Scheme.Modules.ihomEval_smul_left, Scheme.Modules.ihomEval_smul_left,
    ← Scheme.Modules.map_ihomEval, ← Scheme.Modules.map_ihomEval, h]
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_dual_eq_of_ihomEval_eq
end ProofImplementation

end IsFrameOn_dual_eq_of_ihomEval_eq

section IsFrameOn_exists_isFrameOn_dual

/-!
# Scheme Modules Is Frame On exists is Frame On dual
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_exists_isFrameOn_dual

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.Opposite

noncomputable section

namespace DualFrameAux

variable {X : Scheme.{u}}

lemma presheaf_map_map (M : X.Modules) {A B C : X.Opens} (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A) (x :
  Γ(M, A)) :
    M.presheaf.map g.op (M.presheaf.map f.op x) = M.presheaf.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (g ≫ f) k]

variable {P : X.Modules} {U V : X.Opens} {p : Γ(P, U)} (hp : Scheme.Modules.IsFrameOn p V) (hVU :
  V ≤ U)

include hp in
lemma bij {W : X.Opens} (hW : W ≤ V) : Function.Bijective fun g : Γ(X, W) => g • P.presheaf.map
  (homOfLE ((hW : _ ≤ V).trans hVU)).op p :=
  hp (hW.trans hVU) hW

/-- The coefficient of a local section in the specified frame. -/
noncomputable def coef {W : X.Opens} (hW : W ≤ V) (m : Γ(P, W)) : Γ(X, W) :=
  (Equiv.ofBijective _ (bij hp hVU hW)).symm m

lemma coef_smul_pr {W : X.Opens} (hW : W ≤ V) (m : Γ(P, W)) : coef hp hVU hW m • P.presheaf.map
  (homOfLE ((hW : _ ≤ V).trans hVU)).op p = m :=
  Equiv.ofBijective_apply_symm_apply _ (bij hp hVU hW) m

lemma coef_eq_of_smul_eq {W : X.Opens} (hW : W ≤ V) {m : Γ(P, W)} {g : Γ(X, W)} (h : g •
  P.presheaf.map (homOfLE ((hW : _ ≤ V).trans hVU)).op p = m) :
    coef hp hVU hW m = g :=
  (bij hp hVU hW).1 ((coef_smul_pr hp hVU hW m).trans h.symm)

lemma coef_pr {W : X.Opens} (hW : W ≤ V) : coef hp hVU hW (P.presheaf.map (homOfLE ((hW : _ ≤
  V).trans hVU)).op p) = 1 :=
  coef_eq_of_smul_eq hp hVU hW (one_smul _ _)

lemma coef_add {W : X.Opens} (hW : W ≤ V) (m m' : Γ(P, W)) :
    coef hp hVU hW (m + m') = coef hp hVU hW m + coef hp hVU hW m' :=
  coef_eq_of_smul_eq hp hVU hW (by rw [add_smul, coef_smul_pr, coef_smul_pr])

lemma coef_smul {W : X.Opens} (hW : W ≤ V) (r : Γ(X, W)) (m : Γ(P, W)) :
    coef hp hVU hW (r • m) = r * coef hp hVU hW m :=
  coef_eq_of_smul_eq hp hVU hW (by rw [mul_smul, coef_smul_pr])

lemma map_coef {W W' : X.Opens} (hW : W ≤ V) (i : W' ⟶ W) (m : Γ(P, W)) :
    X.presheaf.map i.op (coef hp hVU hW m) = coef hp hVU (i.le.trans hW) (P.presheaf.map i.op m)
      := by
  symm
  apply coef_eq_of_smul_eq hp hVU (i.le.trans hW)
  have h := congrArg (P.presheaf.map i.op) (coef_smul_pr hp hVU hW m)
  rw [Scheme.Modules.map_smul] at h
  rw [← h]
  congr 1
  exact (presheaf_map_map P _ _ _ p).symm

/-- The linear coefficient map with values in sections of the unit sheaf. -/
noncomputable def coefLin {W : X.Opens} (hW : W ≤ V) : Γ(P, W) →ₗ[Γ(X, W)] Γ(𝟙_ X.Modules, W) where
  toFun m := coef hp hVU hW m • Scheme.Modules.unitSection W
  map_add' m m' := by rw [coef_add, add_smul]
  map_smul' r m := by rw [coef_smul, mul_smul, RingHom.id_apply]

lemma coefLin_apply {W : X.Opens} (hW : W ≤ V) (m : Γ(P, W)) :
    coefLin hp hVU hW m = coef hp hVU hW m • Scheme.Modules.unitSection W := rfl

/-- The natural family of coefficient maps on subopens. -/
noncomputable def coefFamily :
    PresheafOfModules.InternalHom.naturalFamilies ((Scheme.Modules.toPMod X).obj P)
      ((Scheme.Modules.toPMod X).obj (𝟙_ X.Modules)) (op V) :=
  ⟨fun W f => coefLin hp hVU (W := W.unop) (f.unop.le : W.unop ≤ V), by
    intro W W' f g m
    change (𝟙_ X.Modules).presheaf.map g (coef hp hVU _ m • Scheme.Modules.unitSection W.unop) =
      coef hp hVU _ (P.presheaf.map g m) • Scheme.Modules.unitSection W'.unop
    rw [show g = g.unop.op from rfl, Scheme.Modules.map_smul, Scheme.Modules.map_unitSection]
    congr 1
    exact map_coef hp hVU _ g.unop m⟩

lemma coefFamily_app {W : (X.Opens)ᵒᵖ} (f : op V ⟶ W) (m : Γ(P, W.unop)) :
    (coefFamily hp hVU).1 f m = coef hp hVU (f.unop.le : W.unop ≤ V) m •
      Scheme.Modules.unitSection W.unop := rfl

/-- The dual section corresponding to the natural family of coefficient maps. -/
noncomputable def dualSection : Γ(Scheme.Modules.dual P, V) :=
  (SheafOfModules.ihomSectionsEquivFamily X.sheaf.obj X.ringCatSheaf.property P (𝟙_ X.Modules) (op
    V)).symm
    (coefFamily hp hVU)

lemma ihomEval_map_dualSection {W : X.Opens} (hW : W ≤ V) (m : Γ(P, W)) :
    Scheme.Modules.ihomEval P (𝟙_ X.Modules) W m
        ((Scheme.Modules.dual P).presheaf.map (homOfLE hW).op (dualSection hp hVU)) =
      coef hp hVU hW m • Scheme.Modules.unitSection W := by
  have h := SheafOfModules.ihomSectionsEquivFamily_app_eq_ihomEval X.sheaf.obj
    X.ringCatSheaf.property
    (M := P) (N := 𝟙_ X.Modules) (homOfLE hW).op (dualSection hp hVU) m
  rw [dualSection, AddEquiv.apply_symm_apply] at h
  exact h.symm

end DualFrameAux

end

open DualFrameAux in
theorem _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_isFrameOn_dual
    {X : Scheme.{u}} {P : X.Modules} {U V : X.Opens} {p : Γ(P, U)}
    (hp : Scheme.Modules.IsFrameOn p V) (hVU : V ≤ U) :
    ∃ q : Γ(Scheme.Modules.dual P, V), Scheme.Modules.IsFrameOn q V ∧
      Scheme.Modules.ihomEval P (𝟙_ X.Modules) V (P.presheaf.map (homOfLE hVU).op p) q =
        Scheme.Modules.unitSection V := by
  classical
  refine ⟨dualSection hp hVU, ?_, ?_⟩
  · intro W hWV hWV'
    have hq : ∀ (g : Γ(X, W)),
        Scheme.Modules.ihomEval P (𝟙_ X.Modules) W (P.presheaf.map (homOfLE ((hWV' : _ ≤ V).trans
          hVU)).op p)
          (g • (Scheme.Modules.dual P).presheaf.map (homOfLE hWV).op (dualSection hp hVU)) =
          g • Scheme.Modules.unitSection W := fun g => by
      rw [Scheme.Modules.ihomEval_smul_right, ihomEval_map_dualSection hp hVU hWV (P.presheaf.map
        (homOfLE ((hWV' : _ ≤ V).trans hVU)).op p)]
      rw [show coef hp hVU hWV (P.presheaf.map (homOfLE ((hWV' : _ ≤ V).trans hVU)).op p) = 1 from
        coef_pr hp hVU hWV', one_smul]
    refine ⟨fun g g' hgg' => ?_, fun t => ?_⟩
    · have h := congrArg (Scheme.Modules.ihomEval P (𝟙_ X.Modules) W (P.presheaf.map (homOfLE
        ((hWV' : _ ≤ V).trans hVU)).op p)) hgg'
      change Scheme.Modules.ihomEval P (𝟙_ X.Modules) W (P.presheaf.map (homOfLE ((hWV' : _ ≤
        V).trans hVU)).op p) (g • _) =
        Scheme.Modules.ihomEval P (𝟙_ X.Modules) W (P.presheaf.map (homOfLE ((hWV' : _ ≤ V).trans
          hVU)).op p) (g' • _) at h
      rw [hq, hq] at h
      exact Scheme.Modules.smul_unitSection_bijective.1 h
    · let g : Γ(X, W) := Scheme.Modules.ihomEval P (𝟙_ X.Modules) W (P.presheaf.map (homOfLE
        ((hWV' : _ ≤ V).trans hVU)).op p) t
      refine ⟨g, ?_⟩
      change g • (Scheme.Modules.dual P).presheaf.map (homOfLE hWV).op (dualSection hp hVU) = t
      apply Scheme.Modules.ihom_sections_ext
      intro W' i m
      have hm : m = coef hp hVU (i.le.trans hWV') m • P.presheaf.map (homOfLE ((i.le.trans hWV' :
        _ ≤ V).trans hVU)).op p :=
        (coef_smul_pr hp hVU (i.le.trans hWV') m).symm
      rw [hm, Scheme.Modules.ihomEval_smul_left, Scheme.Modules.ihomEval_smul_left]
      congr 1
      rw [Scheme.Modules.map_smul, DualFrameAux.presheaf_map_map (Scheme.Modules.dual P) _ _
        (homOfLE (i.le.trans hWV)),
        Scheme.Modules.ihomEval_smul_right, ihomEval_map_dualSection hp hVU (i.le.trans hWV)
          (P.presheaf.map (homOfLE ((i.le.trans hWV' : _ ≤ V).trans hVU)).op p),
        show coef hp hVU (i.le.trans hWV) (P.presheaf.map (homOfLE ((i.le.trans hWV' : _ ≤
          V).trans hVU)).op p) = 1 from coef_pr hp hVU _, one_smul]
      rw [show P.presheaf.map (homOfLE ((i.le.trans hWV' : _ ≤ V).trans hVU)).op p =
          P.presheaf.map i.op (P.presheaf.map (homOfLE ((hWV' : _ ≤ V).trans hVU)).op p) from
        (DualFrameAux.presheaf_map_map P _ _ _ p).symm, ← Scheme.Modules.map_ihomEval]
      rw [Scheme.Modules.smul_unitSection]
      have h2 := Scheme.Modules.map_smul (𝟙_ X.Modules) i g (Scheme.Modules.unitSection W)
      rw [Scheme.Modules.smul_unitSection, Scheme.Modules.map_unitSection,
        Scheme.Modules.smul_unitSection] at h2
      exact h2.symm
  · have h := ihomEval_map_dualSection hp hVU (le_refl V) (P.presheaf.map (homOfLE ((le_refl V : _
      ≤ V).trans hVU)).op p)
    rw [show coef hp hVU (le_refl V) (P.presheaf.map (homOfLE ((le_refl V : _ ≤ V).trans hVU)).op
      p) = 1 from coef_pr hp hVU _, one_smul] at h
    have hid : (Scheme.Modules.dual P).presheaf.map (homOfLE (le_refl V)).op (dualSection hp hVU)
      = dualSection hp hVU := by
      rw [show (homOfLE (le_refl V)).op = 𝟙 _ from Subsingleton.elim _ _,
        CategoryTheory.Functor.map_id]; rfl
    rw [hid] at h
    exact h
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_exists_isFrameOn_dual
end ProofImplementation

end IsFrameOn_exists_isFrameOn_dual

section IsFrameOn_exists_basis_smul_pushforward

/-!
# Scheme Modules Is Frame On exists basis smul pushforward
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.PushforwardFrameBasis

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_basis_smul_pushforward
    {X Y : Scheme.{u}} (π : X ⟶ Y) {L : X.Modules} {V : Y.Opens} {d : ℕ}
    (e : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), V))
    (he : ∀ (W : Y.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin d) Γ(Y, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)).presheaf.map (homOfLE
          hW).op (e i))
    {s : Γ(L, π ⁻¹ᵁ V)} (hs : Scheme.Modules.IsFrameOn s (π ⁻¹ᵁ V)) :
    ∀ (W : Y.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin d) Γ(Y, W) Γ((Scheme.Modules.pushforward π).obj L, W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj L).presheaf.map (homOfLE hW).op
          (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ V) from e i) • s)
            := by
  intro W hW
  obtain ⟨b₀, hb₀⟩ := he W hW
  have hWV : π ⁻¹ᵁ W ≤ π ⁻¹ᵁ V := fun x hx => hW hx
  let sW : Γ(L, π ⁻¹ᵁ W) := L.presheaf.map (homOfLE hWV).op s
  have hbij : Function.Bijective fun g : Γ(X, π ⁻¹ᵁ W) => g • sW := hs hWV hWV
  let ψ : Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), W) ≃ₗ[Γ(Y, W)]
      Γ((Scheme.Modules.pushforward π).obj L, W) :=
    { toFun := fun g => (show Γ((Scheme.Modules.pushforward π).obj L, W) from (show Γ(X, π ⁻¹ᵁ W)
      from g) • sW)
      map_add' := fun g g' => by
        change ((show Γ(X, π ⁻¹ᵁ W) from g) + (show Γ(X, π ⁻¹ᵁ W) from g')) • sW = _
        rw [add_smul]; rfl
      map_smul' := fun r g => by
        change ((π.app W).hom r * (show Γ(X, π ⁻¹ᵁ W) from g)) • sW =
          (π.app W).hom r • ((show Γ(X, π ⁻¹ᵁ W) from g) • sW)
        rw [mul_smul]
      invFun := fun m => (Equiv.ofBijective _ hbij).symm (show Γ(L, π ⁻¹ᵁ W) from m)
      left_inv := fun g => (Equiv.ofBijective _ hbij).symm_apply_apply (show Γ(X, π ⁻¹ᵁ W) from g)
      right_inv := fun m => (Equiv.ofBijective _ hbij).apply_symm_apply (show Γ(L, π ⁻¹ᵁ W) from
        m) }
  refine ⟨b₀.map ψ, fun i => ?_⟩
  rw [Module.Basis.map_apply, hb₀ i]
  simp only [Scheme.Modules.pushforward_obj_presheaf_map]
  set j : π ⁻¹ᵁ W ⟶ π ⁻¹ᵁ V := (TopologicalSpace.Opens.map π.base).map (homOfLE hW) with hj
  have hsW : sW = L.presheaf.map j.op s := congrArg (fun k => L.presheaf.map k s)
    (Subsingleton.elim _ _)
  have h1 : (𝟙_ X.Modules).presheaf.map j.op (e i) =
      (show Γ(𝟙_ X.Modules, π ⁻¹ᵁ W) from X.presheaf.map j.op (show Γ(X, π ⁻¹ᵁ V) from e i)) := by
    have h := Scheme.Modules.map_smul (𝟙_ X.Modules) j (show Γ(X, π ⁻¹ᵁ V) from e i)
      (Scheme.Modules.unitSection (π ⁻¹ᵁ V))
    rw [Scheme.Modules.smul_unitSection, Scheme.Modules.map_unitSection,
      Scheme.Modules.smul_unitSection] at h
    exact h
  change (show Γ(X, π ⁻¹ᵁ W) from (𝟙_ X.Modules).presheaf.map j.op (e i)) • sW =
    L.presheaf.map j.op ((show Γ(X, π ⁻¹ᵁ V) from e i) • s)
  rw [h1, Scheme.Modules.map_smul, hsW]
end AlgebraicCurves.Geometry.Sheaves.Proofs.PushforwardFrameBasis
end ProofImplementation

end IsFrameOn_exists_basis_smul_pushforward

section IsFrameOn_exists_isFrameOn_normModule

/-!
# Scheme Modules Is Frame On exists is Frame On norm Module
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.NormFrameExistence

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.Opposite

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_isFrameOn_normModule
    {X Y : Scheme.{u}} (π : X ⟶ Y) (d : ℕ) {L : X.Modules} {V : Y.Opens}
    (e : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), V))
    (he : ∀ (W : Y.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin d) Γ(Y, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)).presheaf.map (homOfLE
          hW).op (e i))
    {s : Γ(L, π ⁻¹ᵁ V)} (hs : Scheme.Modules.IsFrameOn s (π ⁻¹ᵁ V)) :
    ∃ q : Γ(Scheme.Modules.dual (Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj (𝟙_
      X.Modules))), V),
      Scheme.Modules.IsFrameOn q V ∧
      Scheme.Modules.ihomEval (Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj (𝟙_
        X.Modules)))
          (𝟙_ Y.Modules) V
        (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
            ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj
              (𝟙_ X.Modules)).val)).app
          (op V)
          (show ((Scheme.Modules.presheafExteriorPower Y d).obj
              ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)).val).obj (op V) from
                exteriorPower.ιMulti (M := Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules),
                V)) Γ(Y, V) d e))
        q = Scheme.Modules.unitSection V ∧
      Scheme.Modules.IsFrameOn (M := Scheme.Modules.normModule π d L)
        (Scheme.Modules.tensorSections
          (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
              ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj
                L).val)).app (op V)
            (show ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward
              π).obj L).val).obj (op V)
              from exteriorPower.ιMulti (M := Γ((Scheme.Modules.pushforward π).obj L, V)) Γ(Y, V) d
                (fun i => (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ
                  V) from e i) • s))))
          q)
        V := by
  have hE := Scheme.Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti
    (M := (Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)) e he
  obtain ⟨q, hq, hq1⟩ := hE.exists_isFrameOn_dual (le_refl V)
  have hES := Scheme.Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti
    (M := (Scheme.Modules.pushforward π).obj L)
    (fun i => (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ V) from e i)
      • s))
    (Scheme.Modules.IsFrameOn.exists_basis_smul_pushforward π e he hs)
  refine ⟨q, hq, ?_, ?_⟩
  · have hid : ∀ (M : Y.Modules) (x : Γ(M, V)), M.presheaf.map (homOfLE (le_refl V)).op x = x :=
      fun M x => by
      rw [show (homOfLE (le_refl V)).op = 𝟙 _ from Subsingleton.elim _ _,
        CategoryTheory.Functor.map_id]; rfl
    exact (congrArg
      (fun x : Γ(Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)), V) =>
        Scheme.Modules.ihomEval
          (Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)))
          (𝟙_ Y.Modules) V x q)
      (hid _ _)).symm.trans hq1
  · exact hES.tensorSections hq
end AlgebraicCurves.Geometry.Sheaves.Proofs.NormFrameExistence
end ProofImplementation

end IsFrameOn_exists_isFrameOn_normModule
