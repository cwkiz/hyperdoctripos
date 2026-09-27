
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Category.HeytAlg
import Mathlib.Order.GaloisConnection.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! Applicative definitions for a hyperdoctrine.
   ( P : Cᵒᵖ ⥤ HeytAlg.{u} )
A hyperdoctrine on a category is a functor from the opposite of C to a logic
here being a Heyting algebra.

For every morphism f: A -> B, hyperdoctrine P(f):
    -- P assigns to each X in T, the Heyting algebra of predicates
    on X,
    and to each morphism f:X->Y in T, f* := P(f): P(Y) -> P(X) is the substitution functor which:
    -- has a left adjoint applying existential quantifier
    -- has a right adjoint applying universal quantifier

    GaloisConnection for they are quantifiers over adjoints functors.
 -/

open CategoryTheory

universe u v

structure Hyperdoctrine (C : Type v) [Category.{v} C] [Limits.HasBinaryProducts C] where
P : Cᵒᵖ ⥤ HeytAlg.{u}

exists_ : ∀ {X Y : C} (_f : X ⟶ Y), (P.obj (Opposite.op X) → P.obj (Opposite.op Y))
forall_ : ∀ {X Y : C} (_f : X ⟶ Y), (P.obj (Opposite.op X) → P.obj (Opposite.op Y))
eq_ : ∀ X : C, P.obj ((Opposite.op (X ⨯ X))) :=
  fun X => exists_ (Limits.prod.lift (𝟙 X) (𝟙 X)) ⊤

existsAdj : ∀ {X Y : C} (f : X ⟶ Y),
    GaloisConnection (exists_ f) (P.map (Opposite.op f))

forallAdj : ∀ {X Y : C} (f : X ⟶ Y),
    GaloisConnection (P.map (Opposite.op f)) (forall_ f)

BeckChevalleyExists :
    ∀ {A B C₀ D : C} {f : A ⟶ B} {g : A ⟶ C₀} {h : B ⟶ D} {k : C₀ ⟶ D}
      (_pb : IsPullback f g h k) (p : P.obj (Opposite.op B)),
      exists_ g (P.map f.op p) = P.map k.op (exists_ h p)

BeckChevalleyForAll :
    ∀ {A B C₀ D : C} {f : A ⟶ B} {g : A ⟶ C₀} {h : B ⟶ D} {k : C₀ ⟶ D}
      (_pb : IsPullback f g h k) (p : P.obj (Opposite.op B)),
      forall_ g (P.map f.op p) = P.map k.op (forall_ h p)

Frobenius :
  ∀ {X Y : C} (f : X ⟶ Y) (q : P.obj (Opposite.op Y)) (p : P.obj (Opposite.op X)),
    exists_ f (P.map f.op q ⊓ p) = q ⊓ exists_ f p
