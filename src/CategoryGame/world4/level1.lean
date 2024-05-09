import category_theory.category.default
import category_theory.functor
import category_theory.isomorphism


universes v₁ v₂ u₁ u₂  -- The order in this declaration matters: v often needs to be explicitly specified while u often can be omitted

namespace category_theory

variables (C : Type u₁) [category.{v₁} C]
variables (D : Type u₂) [category.{v₂} D]

/-
# Functor world

## Level 1: Definition of functor

A functor `F : C ⥤ D` between categories `C` and `D` consists of
  * an object `F.obj X ∈ D` for all objects `X ∈ C`
  * a morphism `Ff : F.obj X ⟶ F.obj Y` for each morphism `f : X ⟶ Y`, where the domain and codomain of `Ff` are, respectively, equal to `F` applied to the domain and codomain of `f`.
The assignments are required to satisfy the following two functoriality axioms:
  * for any composable pair of morphisms `f, g` in `C`, `F.map f ≫ F.map g = F.map (f ≫ g)`.
  * for each object `X` in `C`, `F.map (𝟙 X) : 𝟙 (F.obj X)`.
In other words, a functor consists of a mapping on objects and a mapping on morphisms that preserves all of the structure of a category, namely domains and codomains, composition, and identities.
  -/

  /- Axiom : 
    F.map f ≫ F.map g = F.map (f ≫ g)-/
  /- Axiom:
    F.map (𝟙 X) : 𝟙 (F.obj X)-/

/- Lemma
If $$f : X ⟶ Y$$ and $$g : X ⟶ Y$$ are monomorphisms, then $$f ≫ g : X ⟶ Z$$ is a monomorphism.
-/
lemma map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [epi (f ≫ g)] : epi g :=
begin
    split,
    intros W h l hyp,
    rw ← cancel_epi (f ≫ g),
    rw category.assoc,
    rw hyp,
    rw ← category.assoc,
end

end category_theory