/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Hausdorff completions of uniform spaces; lifting the group and ring structure.

The goal is to construct a left-adjoint to the inclusion of complete Hausdorff uniform spaces
into all uniform spaces. Any uniform space `α` gets a completion `completion α` and a morphism
(ie. uniformly continuous map) `completion : α → completion α` which solves the universal
mapping problem of factorizing morphisms from `α` to any complete Hausdorff uniform space `β`.
It means any uniformly continuous `f : α → β` gives rise to a unique morphism
`completion.map f : completion α → β` such that `f = completion.extension f ∘ completion α`.
Actually `completion.extension f` is defined for all maps from `α` to `β` but it has the desired
properties only if `f` is uniformly continuous.

Beware that `completion α` is not injective if `α` is not Hausdorff. But its image is always
dense. The adjoint functor acting on morphisms is then constructed by the usual abstract nonsense.
For every uniform spaces `α` and `β`, it turns `f : α → β` into a morphism
  `completion.map f : completion α → completion β`
such that
  `coe ∘ f = (completion.map f) ∘ coe`
provided `f` is uniformly continuous. This construction is compatible with composition.

In this file we introduce the following concepts:

* `separation_setoid α`: to construct the quotient over all elements which are topologically not
  distinguishable.

* `Cauchy α` the uniform completion of the uniform space `α` (using Cauchy filters). These are not
  minimal filters.

* `completion α := quotient (separation_setoid (Cauchy α))` the Hausdorff completion.

* lift topological groups (using `uniform_add_group`) to the complete group structure.

* lift topological rings (using `uniform_add_group` and `topological_ring`) to the complete ring structure.

This formalization is mostly based on
  N. Bourbaki: General Topology
  I. M. James: Topologies and Uniformities
From a slightly different perspective in order to reuse material in analysis.topology.uniform_space.
-/
import tactic.ring
import data.set.basic data.set.function
import algebra.pi_instances
import analysis.topology.uniform_space analysis.topology.topological_structures
import ring_theory.ideals

noncomputable theory
local attribute [instance] classical.prop_decidable

lemma quot_mk_quotient_mk {α :Type*} [setoid α] (a : α) : quot.mk setoid.r a = ⟦a⟧ :=
rfl

def habitant_of_quotient_habitant {α : Type*} {s : setoid α} (x : quotient s) : α :=
(classical.inhabited_of_nonempty $ (nonempty_quotient_iff s).1 ⟨x⟩).default

lemma continuous_of_const {α : Type*} {β : Type*}
  [topological_space α] [topological_space β]
  {f : α → β} (h : ∀a b, f a = f b) :
  continuous f :=
λ s _, by convert @is_open_const _ _ (∃ a, f a ∈ s); exact
  set.ext (λ a, ⟨λ fa, ⟨_, fa⟩,
    λ ⟨b, fb⟩, show f a ∈ s, from h b a ▸ fb⟩)


section
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} 

def function.comp₂ (f : α → β → γ) (g : γ → δ) : α → β → δ := λ  x y, g (f x y)

notation g `∘₂` f := function.comp₂ f g

lemma function.uncurry_comp₂ (f : α → β → γ) (g : γ → δ) : 
  function.uncurry (g ∘₂ f) = (g ∘ function.uncurry f) := 
begin
  ext x,
  cases x,
  simp[function.comp₂, function.uncurry],
end
end

section
open topological_space
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} 

variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

def continuous₂ (f : α → β → γ) := continuous (function.uncurry f)

lemma continuous₂_def (f : α → β → γ) : continuous₂ f ↔ continuous (function.uncurry f) := iff.rfl

lemma continuous₂_curry (f : α × β → γ) : continuous₂ (function.curry f) ↔ continuous f :=
by rw  [←function.uncurry_curry f] {occs := occurrences.pos [2]} ; refl

lemma continuous₂.comp {f : α → β → γ} {g : γ → δ}
  (hf : continuous₂ f)(hg : continuous g) :
continuous₂ (g ∘₂ f) :=
begin
  unfold continuous₂,
  rw function.uncurry_comp₂,
  exact hf.comp hg
end
end

section
open uniform_space
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} 

variables [uniform_space α] [uniform_space β] [uniform_space γ] [uniform_space δ]

def uniform_continuous₂ (f : α → β → γ) := uniform_continuous (function.uncurry f)

lemma uniform_continuous₂_def (f : α → β → γ) : uniform_continuous₂ f ↔ uniform_continuous (function.uncurry f) := iff.rfl

lemma uniform_continuous₂_curry (f : α × β → γ) : uniform_continuous₂ (function.curry f) ↔ uniform_continuous f :=
by rw  [←function.uncurry_curry f] {occs := occurrences.pos [2]} ; refl

lemma uniform_continuous₂.comp {f : α → β → γ} {g : γ → δ}
  (hf : uniform_continuous₂ f)(hg : uniform_continuous g) :
uniform_continuous₂ (g ∘₂ f) :=
begin
  unfold uniform_continuous₂,
  rw function.uncurry_comp₂,
  exact hf.comp hg
end
end

open filter set
universes u v w x

def  uniform_space.separation_setoid (α : Type u) [uniform_space α] : setoid α :=
⟨λx y, (x, y) ∈ separation_rel α, separated_equiv⟩

section
variables {α : Type u} {β : Type v} {γ : Type w}
variables [uniform_space α] [uniform_space β] [uniform_space γ]
local attribute [instance] uniform_space.separation_setoid

def uniform_space.separated_map (f : α → β) : Prop := ∀ x y, x ≈ y → f x ≈ f y

def uniform_space.separated_map₂ (f : α → β → γ) : Prop := uniform_space.separated_map (function.uncurry f)

--∀ x x' y y', x ≈ x' → y ≈ y' → f x y ≈ f x' y'

end

section
open uniform_space
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type*}
variables [uniform_space α] [uniform_space β] [uniform_space γ] [uniform_space δ]


local attribute [instance] uniform_space.separation_setoid

lemma uniform_space.separated_map.comp {f : α → β} {g : β → γ} (hf : separated_map f) (hg : separated_map g) :
separated_map (g ∘ f) := assume x y h, hg _ _ (hf x y h)

lemma uniform_space.separated_map.comp₂ {f : α → β → γ} {g : γ → δ} (hf : separated_map₂ f) (hg : separated_map g) :
separated_map₂ (g ∘₂ f) := 
begin
  unfold separated_map₂,
  rw function.uncurry_comp₂,
  exact hf.comp hg
end

lemma uniform_space.separated_map.eqv_of_separated {f : α → β} {x y : α} (hf : uniform_space.separated_map f) 
  (h : x ≈ y) : f x ≈ f y := hf x y h

lemma uniform_space.separated_map.eq_of_separated [separated β] {f : α → β} {x y : α} (hf : uniform_space.separated_map f) 
  (h : x ≈ y) : f x = f y := separated_def.1 ‹_›  _ _ (hf x y h)

lemma uniform_continuous.separated_map {f : α → β} (H : uniform_continuous f) :
  uniform_space.separated_map f := assume x y h s Hs, h _ (H Hs)

lemma uniform_continuous.eqv_of_separated {f : α → β} (H : uniform_continuous f) {x y : α} (h : x ≈ y) : 
  f x ≈ f y
 := H.separated_map _ _ h

lemma uniform_continuous.eq_of_separated [separated β] {f : α → β} (H : uniform_continuous f) {x y : α} (h : x ≈ y) : 
  f x = f y
 := H.separated_map.eq_of_separated h  
end


namespace uniform_space
local attribute [instance] uniform_space.separation_setoid
variables {α : Type u} {β : Type v} {γ : Type w}
variables [uniform_space α] [uniform_space β] [uniform_space γ]

lemma separation_prod {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) ≈ (a₂, b₂) ↔ a₁ ≈ a₂ ∧ b₁ ≈ b₂ :=
begin
  split,
  { assume h,
    exact ⟨uniform_continuous_fst.separated_map _ _ h,
           uniform_continuous.separated_map uniform_continuous_snd _ _ h⟩ },
  { rintros ⟨eqv_α, eqv_β⟩ r r_in,
    rw uniformity_prod at r_in,
    rcases r_in with ⟨t_α, ⟨r_α, r_α_in, h_α⟩, t_β, ⟨r_β, r_β_in, h_β⟩, H⟩,

    let p_α := λ(p : (α × β) × (α × β)), (p.1.1, p.2.1),
    let p_β := λ(p : (α × β) × (α × β)), (p.1.2, p.2.2),
    have key_α : p_α ((a₁, b₁), (a₂, b₂)) ∈ r_α, { simp [p_α, eqv_α r_α r_α_in] },
    have key_β : p_β ((a₁, b₁), (a₂, b₂)) ∈ r_β, { simp [p_β, eqv_β r_β r_β_in] },
    exact H ⟨h_α key_α, h_β key_β⟩ },
end

instance separated.prod [separated α] [separated β] : separated (α × β) :=
separated_def.2 $ assume x y H, prod.ext
  (uniform_continuous_fst.eq_of_separated H)
  (uniform_continuous_snd.eq_of_separated H)

/-- separation space -/
@[reducible]
def sep_quot (α : Type*) [uniform_space α] := quotient (separation_setoid α)

namespace sep_quot

def mk {α : Type u} [uniform_space α] : α → sep_quot α := quotient.mk

instance {α : Type u} [u : uniform_space α] : uniform_space (sep_quot α) :=
{ to_topological_space := u.to_topological_space.coinduced (λx, ⟦x⟧),
  uniformity := map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) uniformity,
  refl := le_trans (by simp [quotient.exists_rep]) (filter.map_mono refl_le_uniformity),
  symm := tendsto_map' $
    by simp [prod.swap, (∘)]; exact tendsto_swap_uniformity.comp tendsto_map,
  comp := calc (map (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) uniformity).lift' (λs, comp_rel s s) =
          uniformity.lift' ((λs, comp_rel s s) ∘ image (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧))) :
      map_lift'_eq2 $ monotone_comp_rel monotone_id monotone_id
    ... ≤ uniformity.lift' (image (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) ∘ (λs:set (α×α), comp_rel s (comp_rel s s))) :
      lift'_mono' $ assume s hs ⟨a, b⟩ ⟨c, ⟨⟨a₁, a₂⟩, ha, a_eq⟩, ⟨⟨b₁, b₂⟩, hb, b_eq⟩⟩,
      begin
        simp at a_eq,
        simp at b_eq,
        have h : ⟦a₂⟧ = ⟦b₁⟧, { rw [a_eq.right, b_eq.left] },
        have h : (a₂, b₁) ∈ separation_rel α := quotient.exact h,
        simp [function.comp, set.image, comp_rel, and.comm, and.left_comm, and.assoc],
        exact ⟨a₁, a_eq.left, b₂, b_eq.right, a₂, ha, b₁, h s hs, hb⟩
      end
    ... = map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) (uniformity.lift' (λs:set (α×α), comp_rel s (comp_rel s s))) :
      by rw [map_lift'_eq];
        exact monotone_comp_rel monotone_id (monotone_comp_rel monotone_id monotone_id)
    ... ≤ map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) uniformity :
      map_mono comp_le_uniformity3,
  is_open_uniformity := assume s,
    have ∀a, ⟦a⟧ ∈ s →
        ({p:α×α | p.1 = a → ⟦p.2⟧ ∈ s} ∈ (@uniformity α _).sets ↔
          {p:α×α | p.1 ≈ a → ⟦p.2⟧ ∈ s} ∈ (@uniformity α _).sets),
      from assume a ha,
      ⟨assume h,
        let ⟨t, ht, hts⟩ := comp_mem_uniformity_sets h in
        have hts : ∀{a₁ a₂}, (a, a₁) ∈ t → (a₁, a₂) ∈ t → ⟦a₂⟧ ∈ s,
          from assume a₁ a₂ ha₁ ha₂, @hts (a, a₂) ⟨a₁, ha₁, ha₂⟩ rfl,
        have ht' : ∀{a₁ a₂}, a₁ ≈ a₂ → (a₁, a₂) ∈ t,
          from assume a₁ a₂ h, sInter_subset_of_mem ht h,
        uniformity.sets_of_superset ht $ assume ⟨a₁, a₂⟩ h₁ h₂, hts (ht' $ setoid.symm h₂) h₁,
        assume h, uniformity.sets_of_superset h $ by simp {contextual := tt}⟩,
    begin
      simp [topological_space.coinduced, u.is_open_uniformity, uniformity, forall_quotient_iff],
      exact ⟨λh a ha, (this a ha).mp $ h a ha, λh a ha, (this a ha).mpr $ h a ha⟩
    end }

lemma uniformity_quotient :
  @uniformity (sep_quot α) _ = uniformity.map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) :=
rfl

lemma uniform_continuous_mk :
  uniform_continuous (quotient.mk : α → sep_quot α) :=
le_refl _

lemma uniform_continuous_quotient {f : sep_quot α → β}
  (hf : uniform_continuous (λx, f ⟦x⟧)) : uniform_continuous f :=
hf

lemma comap_quotient_le_uniformity :
  uniformity.comap (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) ≤ uniformity :=
assume t' ht',
let ⟨t, ht, tt_t'⟩ := comp_mem_uniformity_sets ht' in
let ⟨s, hs, ss_t⟩ := comp_mem_uniformity_sets ht in
⟨(λp:α×α, (⟦p.1⟧, ⟦p.2⟧)) '' s,
  (@uniformity α _).sets_of_superset hs $ assume x hx, ⟨x, hx, rfl⟩,
  assume ⟨a₁, a₂⟩ ⟨⟨b₁, b₂⟩, hb, ab_eq⟩,
  have ⟦b₁⟧ = ⟦a₁⟧ ∧ ⟦b₂⟧ = ⟦a₂⟧, from prod.mk.inj ab_eq,
  have b₁ ≈ a₁ ∧ b₂ ≈ a₂, from and.imp quotient.exact quotient.exact this,
  have ab₁ : (a₁, b₁) ∈ t, from (setoid.symm this.left) t ht,
  have ba₂ : (b₂, a₂) ∈ s, from this.right s hs,
  tt_t' ⟨b₁, show ((a₁, a₂).1, b₁) ∈ t, from ab₁,
    ss_t ⟨b₂, show ((b₁, a₂).1, b₂) ∈ s, from hb, ba₂⟩⟩⟩

lemma comap_quotient_eq_uniformity :
  uniformity.comap (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) = uniformity :=
le_antisymm comap_quotient_le_uniformity le_comap_map

instance complete_space_separation [h : complete_space α] :
  complete_space (sep_quot α) :=
⟨assume f, assume hf : cauchy f,
  have cauchy (f.comap (λx, ⟦x⟧)), from
    cauchy_comap comap_quotient_le_uniformity hf $
      comap_neq_bot_of_surj hf.left $ assume b, quotient.exists_rep _,
  let ⟨x, (hx : f.comap (λx, ⟦x⟧) ≤ nhds x)⟩ := complete_space.complete this in
  ⟨⟦x⟧, calc f ≤ map (λx, ⟦x⟧) (f.comap (λx, ⟦x⟧)) : le_map_comap $ assume b, quotient.exists_rep _
    ... ≤ map (λx, ⟦x⟧) (nhds x) : map_mono hx
    ... ≤ _ : continuous_iff_tendsto.mp uniform_continuous_mk.continuous _⟩⟩

instance separated : separated (sep_quot α) :=
set.ext $ assume ⟨a, b⟩, quotient.induction_on₂ a b $ assume a b,
  ⟨assume h,
    have a ≈ b, from assume s hs,
      have s ∈ (uniformity.comap (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧))).sets,
        from comap_quotient_le_uniformity hs,
      let ⟨t, ht, hts⟩ := this in
      hts begin dsimp, exact h t ht end,
    show ⟦a⟧ = ⟦b⟧, from quotient.sound this,

  assume heq : ⟦a⟧ = ⟦b⟧, assume h hs,
  heq ▸ refl_mem_uniformity hs⟩

def lift [separated β] (f : α → β) : sep_quot α → β :=
if h : separated_map f then
  quotient.lift f (λ x x' hxx', h.eq_of_separated hxx')
else
  λ x, f $ habitant_of_quotient_habitant x

lemma continuous_lift [separated β] {f : α → β} (h : continuous f) : continuous (lift f) :=
begin
  by_cases hf : separated_map f,
  { rw [lift, dif_pos hf], apply continuous_quotient_lift _ h, },
  { rw [lift, dif_neg hf], exact continuous_of_const (λ a b, rfl)} 
end

lemma uniform_continuous_lift [separated β] {f : α → β} (hf : uniform_continuous f) : uniform_continuous (lift f) :=
by simp [lift, hf.separated_map] ; exact hf

section sep_quot_lift
variables  [separated β] {f : α → β} (h : separated_map f) 
include h

lemma lift_mk (x : α) : lift f ⟦x⟧ = f x := by simp[lift, h]

lemma unique_lift {g : sep_quot α → β} (hg : uniform_continuous g) (g_mk : ∀ x, g ⟦x⟧ = f x) : g = lift f :=
begin
  ext a,
  cases quotient.exists_rep a with x hx,
  rwa [←hx, lift_mk h x, g_mk x]
end
end sep_quot_lift

def map (f : α → β) : sep_quot α → sep_quot β := lift (quotient.mk ∘ f)

lemma continuous_map {f : α → β} (h : continuous f) : continuous (map f) :=
continuous_lift $ h.comp continuous_quotient_mk

lemma uniform_continuous_map {f : α → β} (hf : uniform_continuous f): uniform_continuous (map f) :=
uniform_continuous_lift (hf.comp uniform_continuous_mk)

lemma map_mk {f : α → β} (h : separated_map f) (a : α) : map f ⟦a⟧ = ⟦f a⟧ :=
by rw [map, lift_mk (h.comp uniform_continuous_mk.separated_map)]

lemma map_unique {f : α → β} (hf : separated_map f)
  {g : sep_quot α → sep_quot β}
  (comm : quotient.mk ∘ f = g ∘ quotient.mk) : map f = g :=
by ext ⟨a⟩;
calc map f ⟦a⟧ = ⟦f a⟧ : map_mk hf a
  ... = g ⟦a⟧ : congr_fun comm a

lemma map_id : map (@id α) = id :=
map_unique uniform_continuous_id.separated_map rfl

lemma map_comp {f : α → β} {g : β → γ} (hf : separated_map f) (hg : separated_map g) :
  map g ∘ map f = map (g ∘ f) :=
(map_unique (hf.comp hg) $ by simp only [(∘), map_mk, hf, hg]).symm

protected def prod  : sep_quot α → sep_quot β → sep_quot (α × β) :=
quotient.lift₂ (λ a b, ⟦(a, b)⟧) $ assume _ _ _ _ h h', quotient.eq.2 (separation_prod.2 ⟨h, h'⟩)

lemma uniform_continuous_prod : uniform_continuous₂ (@sep_quot.prod α β _ _) :=
begin
  unfold uniform_continuous₂,
  unfold uniform_continuous, 
  rw [uniformity_prod_eq_prod, uniformity_quotient, uniformity_quotient, filter.prod_map_map_eq, 
    filter.tendsto_map'_iff, filter.tendsto_map'_iff, uniformity_quotient, uniformity_prod_eq_prod],
  exact tendsto_map
end

@[simp]
lemma prod_mk_mk (a : α) (b : β) : sep_quot.prod ⟦a⟧ ⟦b⟧ = ⟦(a, b)⟧ := rfl

def lift₂ [separated γ] (f : α → β → γ) : sep_quot α → sep_quot β → γ :=
(lift $ function.uncurry f) ∘₂ sep_quot.prod

lemma uniform_continuous_lift₂ [separated γ] {f : α → β → γ} (hf : uniform_continuous₂ f) :
  uniform_continuous₂ (sep_quot.lift₂ f) :=
uniform_continuous_prod.comp $ uniform_continuous_lift hf

@[simp]
lemma lift₂_mk_mk [separated γ] {f : α → β → γ} (h : separated_map₂ f) (a : α) (b : β) : 
  lift₂ f ⟦a⟧ ⟦b⟧ = f a b := lift_mk h _

def map₂ (f : α → β → γ) : sep_quot α → sep_quot β → sep_quot γ :=
lift₂ (quotient.mk ∘₂ f)

lemma uniform_continuous_map₂ {f : α → β → γ} (hf : uniform_continuous₂ f) :
  uniform_continuous₂ (sep_quot.map₂ f) :=
uniform_continuous_lift₂ $ hf.comp uniform_continuous_mk

@[simp]
lemma map₂_mk_mk {f : α → β → γ} (h : separated_map₂ f) (a : α) (b : β) : 
  map₂ f ⟦a⟧ ⟦b⟧ = ⟦f a b⟧ := 
lift₂_mk_mk (uniform_continuous_mk.separated_map.comp₂ h) _ _

lemma map₂_unique {f : α → β → γ} (hf : separated_map₂ f)
  {g : sep_quot α → sep_quot β → sep_quot γ}
  (comm : ∀ a b, ⟦f a b⟧ = g  ⟦a⟧ ⟦b⟧) : map₂ f = g :=
by ext ⟨a⟩ ⟨b⟩ ;
   calc map₂ f ⟦a⟧ ⟦b⟧ = ⟦f a b⟧   : map₂_mk_mk hf a b
                   ... = g ⟦a⟧ ⟦b⟧ : comm a b

variables {δ : Type*} {δ' : Type*} {δ'' : Type*} {ε : Type*}
  [uniform_space δ] [uniform_space δ'] [uniform_space δ''] [uniform_space ε]

lemma continuous_map₂ {f : α → β → γ} (h : continuous₂ f) : continuous₂ (map₂ f) :=
begin
  unfold continuous₂ map₂ lift₂,
  rw function.uncurry_comp₂,
  apply continuous.comp uniform_continuous_prod.continuous,
  apply continuous_lift,
  rw function.uncurry_comp₂,
  apply continuous.comp h continuous_quotient_mk
end

-- Now begins a long series of lemmas for which we use an ad hoc killing tactic. 

meta def sep_quot_tac : tactic unit :=
`[repeat { rintros ⟨x⟩ },
  repeat { rw quot_mk_quotient_mk },
  repeat { rw map_mk },
  repeat { rw map₂_mk_mk },
  repeat { rw map_mk },
  repeat { rw H },
  repeat { assumption } ]

lemma map₂_const_left_eq_map {f : α → β → γ} (hf : separated_map₂ f) 
{g : β → γ} (hg : separated_map g) (a : α)
(H : ∀ b, f a b = g b) : ∀ b, map₂ f ⟦a⟧ b = map g b :=
by sep_quot_tac

lemma map₂_const_right_eq_map {f : α → β → γ} (hf : separated_map₂ f) 
{g : α → γ} (hg : separated_map g) (b : β)
(H : ∀ a, f a b = g a) : ∀ a, map₂ f a ⟦b⟧ = map g a :=
by sep_quot_tac

lemma map₂_map_left_self_const {f : α → β → γ} (hf : separated_map₂ f) 
{g : β → α} (hg : separated_map g) (c : γ)
(H : ∀ b, f (g b) b = c) : ∀ b, map₂ f (map g b) b = ⟦c⟧ :=
by sep_quot_tac

lemma map₂_map_right_self_const {f : α → β → γ} (hf : separated_map₂ f) 
{g : α → β} (hg : separated_map g) (c : γ)
(H : ∀ a, f a (g a) = c) : ∀ a, map₂ f a (map g a) = ⟦c⟧ :=
by sep_quot_tac

lemma map₂_comm {f : α → α → β} (hf : separated_map₂ f) 
(H : ∀ a b, f a b = f b a) : ∀ a b, map₂ f a b = map₂ f b a :=
by sep_quot_tac

lemma map₂_assoc {f : α → β → δ} (hf : separated_map₂ f) 
{f' : β  → γ → δ'} (hf' : separated_map₂ f')
{g : δ → γ → ε} (hg : separated_map₂ g)
{g' : α → δ' → ε} (hg' : separated_map₂ g')
(H : ∀ a b c, g (f a b) c = g' a (f' b c)) : ∀ a b c, map₂ g (map₂ f a b) c = map₂ g' a (map₂ f' b c) :=
by sep_quot_tac

lemma map₂_left_distrib {f : α → β → δ} (hf : separated_map₂ f) 
{f' : α  → γ → δ'} (hf' : separated_map₂ f')
{g : δ → δ' → ε} (hg : separated_map₂ g)
{f'' : β → γ → δ''} (hg : separated_map₂ f'')
{g' : α → δ'' → ε} (hg : separated_map₂ g')
(H : ∀ a b c, g' a (f'' b c) = g (f a b) (f' a c)) : ∀ a b c, 
 map₂ g' a (map₂ f'' b c) = map₂ g (map₂ f a b) (map₂ f' a c) :=
by sep_quot_tac

lemma map₂_right_distrib {f : α → γ → δ} (hf : separated_map₂ f) 
{f' : β → γ → δ'} (hf' : separated_map₂ f')
{g : δ → δ' → ε} (hg : separated_map₂ g)
{f'' : α → β → δ''} (hg : separated_map₂ f'')
{g' : δ'' → γ → ε} (hg : separated_map₂ g')
(H : ∀ a b c, g' (f'' a b) c = g (f a c) (f' b c)) : ∀ a b c, 
 map₂ g' (map₂ f'' a b) c = map₂ g (map₂ f a c) (map₂ f' b c) :=
by sep_quot_tac
end sep_quot

end uniform_space

section uniform_add_group_sep_quot
open uniform_space
variables {α : Type*} [add_group α] [uniform_space α] [uniform_add_group α]
variables {β : Type*} [add_group β] [uniform_space β] [uniform_add_group β]

lemma separated_of_group_hom {f : α → β} [is_add_group_hom f] (hf : continuous f) : 
  separated_map f := (uniform_continuous_of_continuous hf).separated_map

lemma uniform_continuous₂_add : uniform_continuous₂ ((+) : α → α → α) :=
begin
  dsimp [uniform_continuous₂],
  convert @uniform_continuous_add' α _ _ _,
  ext x,
  cases x,
  refl 
end

local attribute [instance] separation_setoid

instance : add_group (sep_quot α) :=
{ add := sep_quot.map₂ (+),
  add_assoc := begin
    apply sep_quot.map₂_assoc ; try { exact uniform_continuous₂_add.separated_map }, 
    exact add_assoc
  end,
  zero := ⟦0⟧,
  zero_add := begin
    change ∀ a : sep_quot α, sep_quot.map₂ has_add.add ⟦0⟧ a = id a,
    rw ←sep_quot.map_id,
    exact sep_quot.map₂_const_left_eq_map uniform_continuous₂_add.separated_map 
      uniform_continuous_id.separated_map _ zero_add
  end,
  add_zero := begin
    change ∀ a : sep_quot α, sep_quot.map₂ has_add.add a ⟦0⟧ = id a,
    rw ←sep_quot.map_id,
    exact sep_quot.map₂_const_right_eq_map  uniform_continuous₂_add.separated_map 
      uniform_continuous_id.separated_map _ add_zero
  end,
  neg := sep_quot.map add_group.neg,
  add_left_neg := sep_quot.map₂_map_left_self_const uniform_continuous₂_add.separated_map
    uniform_continuous_neg'.separated_map (0 : α) add_left_neg }

-- MOVEME
theorem uniform_add_group.mk'' {α} [uniform_space α] [add_group α]
  (h₁ : uniform_continuous₂ ((+) : α → α → α))
  (h₂ : uniform_continuous (λp:α, -p)) : uniform_add_group α :=
⟨(uniform_continuous_fst.prod_mk (uniform_continuous_snd.comp h₂)).comp h₁⟩

instance : uniform_add_group (sep_quot α) :=
uniform_add_group.mk'' (sep_quot.uniform_continuous_map₂ uniform_continuous₂_add) (sep_quot.uniform_continuous_map uniform_continuous_neg')

lemma sep_quot.add_mk (a b : α) : ⟦a⟧ + ⟦b⟧ = ⟦a+b⟧ := 
sep_quot.map₂_mk_mk uniform_continuous₂_add.separated_map _ _

instance sep_quot.is_add_group_hom_mk : is_add_group_hom (quotient.mk : α → sep_quot α) :=
⟨λ a b, eq.symm $ sep_quot.add_mk a b⟩

variables {f : α → β} 

instance sep_quot.is_add_group_hom_lift [separated β]  [hom : is_add_group_hom f] (hf : continuous f) : is_add_group_hom (sep_quot.lift f) :=
⟨begin
  rintros ⟨a⟩ ⟨b⟩,
  repeat { rw quot_mk_quotient_mk },
  rw [sep_quot.add_mk], 
  repeat { rw sep_quot.lift_mk (separated_of_group_hom hf) }, 
  rw hom.add,
end⟩

instance sep_quot.is_add_group_hom_map [hom : is_add_group_hom f](hf : continuous f) : is_add_group_hom (sep_quot.map f) := 
sep_quot.is_add_group_hom_lift (hf.comp continuous_quotient_mk)
end uniform_add_group_sep_quot

section uniform_add_comm_group_sep_quot
open uniform_space
variables {α : Type*} [add_comm_group α] [uniform_space α] [uniform_add_group α]
local attribute [instance] separation_setoid

instance : add_comm_group (sep_quot α) :=
{ add_comm := sep_quot.map₂_comm uniform_continuous₂_add.separated_map add_comm,
  ..uniform_space.sep_quot.add_group, }
end uniform_add_comm_group_sep_quot

section ring_sep_quot
open uniform_space
variables {α : Type*} [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α]
variables {β : Type*} [comm_ring β] [uniform_space β] [uniform_add_group β] [topological_ring β]

local attribute [instance] separation_setoid

lemma separated_map_mul : separated_map₂ ((*) : α → α → α) :=
begin
  rintros ⟨x, y⟩ ⟨x', y'⟩ h,
  cases uniform_space.separation_prod.1 h with hx hy, clear h,
  unfold function.uncurry has_equiv.equiv setoid.r at *,
  rw group_separation_rel x x' at hx,
  rw group_separation_rel y y' at hy,
  rw group_separation_rel (x*y) _,
  rw show x*y - x'*y' = (x - x')*y + x'*(y - y'), by ring,
  let I := ideal.closure (⊥ : ideal α),
  exact I.add_mem (I.mul_mem_right hx) (I.mul_mem_left hy)
end

instance : comm_ring (sep_quot α) :=
{ mul := sep_quot.map₂ (*),
  one := ⟦1⟧,
  one_mul := begin
    change ∀ a : sep_quot α, sep_quot.map₂ (*) ⟦1⟧ a = id a,
    rw ←sep_quot.map_id,
    exact sep_quot.map₂_const_left_eq_map separated_map_mul uniform_continuous_id.separated_map _ one_mul
  end,
  mul_one := begin
    change ∀ a : sep_quot α, sep_quot.map₂ (*) a ⟦1⟧ = id a,
    rw ←sep_quot.map_id,
    exact sep_quot.map₂_const_right_eq_map separated_map_mul uniform_continuous_id.separated_map _ mul_one
  end,
  mul_assoc := begin
    apply sep_quot.map₂_assoc ; try { exact separated_map_mul }, 
    exact mul_assoc
  end,
  mul_comm := sep_quot.map₂_comm separated_map_mul mul_comm,
  left_distrib := begin
    apply sep_quot.map₂_left_distrib ; try { exact separated_map_mul <|> exact uniform_continuous₂_add.separated_map},
    exact left_distrib
  end,
  right_distrib := begin
    apply sep_quot.map₂_right_distrib ; try { exact separated_map_mul <|> exact uniform_continuous₂_add.separated_map},
    exact right_distrib
  end,
  ..uniform_space.sep_quot.add_comm_group }


lemma continuous₂_mul {α : Type*} [ring α] [topological_space α] [topological_ring α] : continuous₂ ((*) : α → α → α) :=
begin
  dsimp [continuous₂],
  convert @continuous_mul' α _ _ _,
  ext x,
  cases x,
  refl 
end

instance : topological_ring (sep_quot α) := 
{ continuous_add := continuous_add',
  continuous_mul := by rw ←continuous₂_curry ; exact sep_quot.continuous_map₂ continuous₂_mul,
  continuous_neg := continuous_neg' }

instance sep_quot.is_ring_hom_mk : is_ring_hom (quotient.mk : α → sep_quot α) :=
{ map_one := rfl,
  map_mul := λ x y, eq.symm (sep_quot.map₂_mk_mk separated_map_mul x y),
  map_add := is_add_group_hom.add _ }

-- Turning the following into an instance wouldn't work because of the continuity assumption
def sep_quot.is_ring_hom_lift [separated β] {f : α → β} [hom : is_ring_hom f] (hf : continuous f) : is_ring_hom (sep_quot.lift f) :=
have sep : separated_map f, from separated_of_group_hom hf,
{ map_one := by change sep_quot.lift f ⟦1⟧ = 1 ; rw [sep_quot.lift_mk sep, hom.map_one ],
  map_mul := begin rintro ⟨x⟩ ⟨y⟩,  rw [quot_mk_quotient_mk, quot_mk_quotient_mk, ←sep_quot.is_ring_hom_mk.map_mul], 
    repeat {rw sep_quot.lift_mk sep} , rw hom.map_mul, end,
  map_add := by haveI := sep_quot.is_add_group_hom_lift hf ; exact is_add_group_hom.add _ }

-- Turning the following into an instance wouldn't work because of the continuity assumption
def sep_quot.is_ring_hom_map {f : α → β} [is_ring_hom f] (hf : continuous f) : is_ring_hom (sep_quot.map f) :=
sep_quot.is_ring_hom_lift (hf.comp continuous_quotient_mk)

end ring_sep_quot
/-- Space of Cauchy filters

This is essentially the completion of a uniform space. The embeddings are the neighbourhood filters.
This space is not minimal, the separated uniform space (i.e. quotiented on the intersection of all
entourages) is necessary for this.
-/
def Cauchy (α : Type u) [uniform_space α] : Type u := { f : filter α // cauchy f }

namespace Cauchy

section
parameters {α : Type u} [uniform_space α]
variables {β : Type v} {γ : Type w}
variables [uniform_space β] [uniform_space γ]

def gen (s : set (α × α)) : set (Cauchy α × Cauchy α) :=
{p | s ∈ (filter.prod (p.1.val) (p.2.val)).sets }

lemma monotone_gen : monotone gen :=
monotone_set_of $ assume p, @monotone_mem_sets (α×α) (filter.prod (p.1.val) (p.2.val))

private lemma symm_gen : map prod.swap (uniformity.lift' gen) ≤ uniformity.lift' gen :=
calc map prod.swap (uniformity.lift' gen) =
  uniformity.lift' (λs:set (α×α), {p | s ∈ (filter.prod (p.2.val) (p.1.val)).sets }) :
  begin
    delta gen,
    simp [map_lift'_eq, monotone_set_of, monotone_mem_sets,
          function.comp, image_swap_eq_preimage_swap]
  end
  ... ≤ uniformity.lift' gen :
    uniformity_lift_le_swap
      (monotone_comp (monotone_set_of $ assume p,
        @monotone_mem_sets (α×α) ((filter.prod ((p.2).val) ((p.1).val)))) monotone_principal)
      begin
        have h := λ(p:Cauchy α×Cauchy α), @filter.prod_comm _ _ (p.2.val) (p.1.val),
        simp [function.comp, h],
        exact le_refl _
      end

private lemma comp_rel_gen_gen_subset_gen_comp_rel {s t : set (α×α)} : comp_rel (gen s) (gen t) ⊆
  (gen (comp_rel s t) : set (Cauchy α × Cauchy α)) :=
assume ⟨f, g⟩ ⟨h, h₁, h₂⟩,
let ⟨t₁, (ht₁ : t₁ ∈ f.val.sets), t₂, (ht₂ : t₂ ∈ h.val.sets), (h₁ : set.prod t₁ t₂ ⊆ s)⟩ :=
  mem_prod_iff.mp h₁ in
let ⟨t₃, (ht₃ : t₃ ∈ h.val.sets), t₄, (ht₄ : t₄ ∈ g.val.sets), (h₂ : set.prod t₃ t₄ ⊆ t)⟩ :=
  mem_prod_iff.mp h₂ in
have t₂ ∩ t₃ ∈ h.val.sets,
  from inter_mem_sets ht₂ ht₃,
let ⟨x, xt₂, xt₃⟩ :=
  inhabited_of_mem_sets (h.property.left) this in
(filter.prod f.val g.val).sets_of_superset
  (prod_mem_prod ht₁ ht₄)
  (assume ⟨a, b⟩ ⟨(ha : a ∈ t₁), (hb : b ∈ t₄)⟩,
    ⟨x,
      h₁ (show (a, x) ∈ set.prod t₁ t₂, from ⟨ha, xt₂⟩),
      h₂ (show (x, b) ∈ set.prod t₃ t₄, from ⟨xt₃, hb⟩)⟩)

private lemma comp_gen :
  (uniformity.lift' gen).lift' (λs, comp_rel s s) ≤ uniformity.lift' gen :=
calc (uniformity.lift' gen).lift' (λs, comp_rel s s) =
    uniformity.lift' (λs, comp_rel (gen s) (gen s)) :
  begin
    rw [lift'_lift'_assoc],
    exact monotone_gen,
    exact (monotone_comp_rel monotone_id monotone_id)
  end
  ... ≤ uniformity.lift' (λs, gen $ comp_rel s s) :
    lift'_mono' $ assume s hs, comp_rel_gen_gen_subset_gen_comp_rel
  ... = (uniformity.lift' $ λs:set(α×α), comp_rel s s).lift' gen :
  begin
    rw [lift'_lift'_assoc],
    exact (monotone_comp_rel monotone_id monotone_id),
    exact monotone_gen
  end
  ... ≤ uniformity.lift' gen : lift'_mono comp_le_uniformity (le_refl _)

instance : uniform_space (Cauchy α) :=
uniform_space.of_core
{ uniformity  := uniformity.lift' gen,
  refl        := principal_le_lift' $ assume s hs ⟨a, b⟩ (a_eq_b : a = b),
    a_eq_b ▸ a.property.right hs,
  symm        := symm_gen,
  comp        := comp_gen }

theorem mem_uniformity {s : set (Cauchy α × Cauchy α)} :
  s ∈ (@uniformity (Cauchy α) _).sets ↔ ∃ t ∈ (@uniformity α _).sets, gen t ⊆ s :=
mem_lift'_sets monotone_gen

theorem mem_uniformity' {s : set (Cauchy α × Cauchy α)} :
  s ∈ (@uniformity (Cauchy α) _).sets ↔ ∃ t ∈ (@uniformity α _).sets,
    ∀ f g : Cauchy α, t ∈ (filter.prod f.1 g.1).sets → (f, g) ∈ s :=
mem_uniformity.trans $ bex_congr $ λ t h, prod.forall

/-- Embedding of `α` into its completion -/
def pure_cauchy (a : α) : Cauchy α :=
⟨pure a, cauchy_pure⟩

lemma uniform_embedding_pure_cauchy : uniform_embedding (pure_cauchy : α → Cauchy α) :=
⟨assume a₁ a₂ h,
  have (pure_cauchy a₁).val = (pure_cauchy a₂).val, from congr_arg _ h,
  have {a₁} = ({a₂} : set α),
    from principal_eq_iff_eq.mp this,
  by simp at this; assumption,

  have (preimage (λ (x : α × α), (pure_cauchy (x.fst), pure_cauchy (x.snd))) ∘ gen) = id,
    from funext $ assume s, set.ext $ assume ⟨a₁, a₂⟩,
      by simp [preimage, gen, pure_cauchy, prod_principal_principal],
  calc comap (λ (x : α × α), (pure_cauchy (x.fst), pure_cauchy (x.snd))) (uniformity.lift' gen)
        = uniformity.lift' (preimage (λ (x : α × α), (pure_cauchy (x.fst), pure_cauchy (x.snd))) ∘ gen) :
      comap_lift'_eq monotone_gen
    ... = uniformity : by simp [this]⟩

lemma pure_cauchy_dense : ∀x, x ∈ closure (range pure_cauchy) :=
assume f,
have h_ex : ∀s∈(@uniformity (Cauchy α) _).sets, ∃y:α, (f, pure_cauchy y) ∈ s, from
  assume s hs,
  let ⟨t'', ht''₁, (ht''₂ : gen t'' ⊆ s)⟩ := (mem_lift'_sets monotone_gen).mp hs in
  let ⟨t', ht'₁, ht'₂⟩ := comp_mem_uniformity_sets ht''₁ in
  have t' ∈ (filter.prod (f.val) (f.val)).sets,
    from f.property.right ht'₁,
  let ⟨t, ht, (h : set.prod t t ⊆ t')⟩ := mem_prod_same_iff.mp this in
  let ⟨x, (hx : x ∈ t)⟩ := inhabited_of_mem_sets f.property.left ht in
  have t'' ∈ (filter.prod f.val (pure x)).sets,
    from mem_prod_iff.mpr ⟨t, ht, {y:α | (x, y) ∈ t'},
      assume y, begin simp, intro h, simp [h], exact refl_mem_uniformity ht'₁ end,
      assume ⟨a, b⟩ ⟨(h₁ : a ∈ t), (h₂ : (x, b) ∈ t')⟩,
        ht'₂ $ prod_mk_mem_comp_rel (@h (a, x) ⟨h₁, hx⟩) h₂⟩,
  ⟨x, ht''₂ $ by dsimp [gen]; exact this⟩,
begin
  simp [closure_eq_nhds, nhds_eq_uniformity, lift'_inf_principal_eq, set.inter_comm],
  exact (lift'_neq_bot_iff $ monotone_inter monotone_const monotone_preimage).mpr
    (assume s hs,
      let ⟨y, hy⟩ := h_ex s hs in
      have pure_cauchy y ∈ range pure_cauchy ∩ {y : Cauchy α | (f, y) ∈ s},
        from ⟨mem_range_self y, hy⟩,
      ne_empty_of_mem this)
end

lemma dense_embedding_pure_cauchy : dense_embedding pure_cauchy :=
uniform_embedding_pure_cauchy.dense_embedding pure_cauchy_dense

lemma nonempty_Cauchy_iff : nonempty (Cauchy α) ↔ nonempty α :=
begin
  split ; rintro ⟨c⟩,
  { have := eq_univ_iff_forall.1 dense_embedding_pure_cauchy.closure_range c,
    have := mem_closure_iff.1 this _ is_open_univ trivial,
    rcases exists_mem_of_ne_empty this with ⟨_, ⟨_, a, _⟩⟩,
    exact ⟨a⟩ },
  { exact ⟨pure_cauchy c⟩ }
end

section
set_option eqn_compiler.zeta true
instance : complete_space (Cauchy α) :=
complete_space_extension
  uniform_embedding_pure_cauchy
  pure_cauchy_dense $
  assume f hf,
  let f' : Cauchy α := ⟨f, hf⟩ in
  have map pure_cauchy f ≤ uniformity.lift' (preimage (prod.mk f')),
    from le_lift' $ assume s hs,
    let ⟨t, ht₁, (ht₂ : gen t ⊆ s)⟩ := (mem_lift'_sets monotone_gen).mp hs in
    let ⟨t', ht', (h : set.prod t' t' ⊆ t)⟩ := mem_prod_same_iff.mp (hf.right ht₁) in
    have t' ⊆ { y : α | (f', pure_cauchy y) ∈ gen t },
      from assume x hx, (filter.prod f (pure x)).sets_of_superset (prod_mem_prod ht' $ mem_pure hx) h,
    f.sets_of_superset ht' $ subset.trans this (preimage_mono ht₂),
  ⟨f', by simp [nhds_eq_uniformity]; assumption⟩
end

instance [inhabited α] : inhabited (Cauchy α) :=
⟨pure_cauchy $ default α⟩

instance [h : nonempty α] : nonempty (Cauchy α) :=
h.rec_on $ assume a, nonempty.intro $ Cauchy.pure_cauchy a

section extend
variables [_root_.complete_space β] [separated β]

def extend (f : α → β) : (Cauchy α → β) :=
if uniform_continuous f then
  dense_embedding_pure_cauchy.extend f
else
  λ x, f (classical.inhabited_of_nonempty $ nonempty_Cauchy_iff.1 ⟨x⟩).default

lemma extend_pure_cauchy {f : α → β} (hf : uniform_continuous f) (a : α) :
  extend f (pure_cauchy a) = f a :=
begin
  rw [extend, if_pos hf],
  exact uniformly_extend_of_emb uniform_embedding_pure_cauchy pure_cauchy_dense _
end

lemma uniform_continuous_extend {f : α → β} : uniform_continuous (extend f) :=
begin
  by_cases hf : uniform_continuous f,
  { rw [extend, if_pos hf],
    exact uniform_continuous_uniformly_extend uniform_embedding_pure_cauchy pure_cauchy_dense hf },
  { rw [extend, if_neg hf],
    exact uniform_continuous_of_const (assume a b, by congr) }
end

end extend

end

theorem Cauchy_eq
  {α : Type*} [inhabited α] [uniform_space α] [complete_space α] [separated α] {f g : Cauchy α} :
  lim f.1 = lim g.1 ↔ (f, g) ∈ separation_rel (Cauchy α) :=
begin
  split,
  { intros e s hs,
    rcases Cauchy.mem_uniformity'.1 hs with ⟨t, tu, ts⟩,
    apply ts,
    rcases comp_mem_uniformity_sets tu with ⟨d, du, dt⟩,
    refine mem_prod_iff.2
      ⟨_, le_nhds_lim_of_cauchy f.2 (mem_nhds_right (lim f.1) du),
       _, le_nhds_lim_of_cauchy g.2 (mem_nhds_left (lim g.1) du), λ x h, _⟩,
    cases x with a b, cases h with h₁ h₂,
    rw ← e at h₂,
    exact dt ⟨_, h₁, h₂⟩ },
  { intros H,
    refine separated_def.1 (by apply_instance) _ _ (λ t tu, _),
    rcases mem_uniformity_is_closed tu with ⟨d, du, dc, dt⟩,
    refine H {p | (lim p.1.1, lim p.2.1) ∈ t}
      (Cauchy.mem_uniformity'.2 ⟨d, du, λ f g h, _⟩),
    rcases mem_prod_iff.1 h with ⟨x, xf, y, yg, h⟩,
    have limc : ∀ (f : Cauchy α) (x ∈ f.1.sets), lim f.1 ∈ closure x,
    { intros f x xf,
      rw closure_eq_nhds,
      exact lattice.neq_bot_of_le_neq_bot f.2.1
        (lattice.le_inf (le_nhds_lim_of_cauchy f.2) (le_principal_iff.2 xf)) },
    have := (closure_subset_iff_subset_of_is_closed dc).2 h,
    rw closure_prod_eq at this,
    refine dt (this ⟨_, _⟩); dsimp; apply limc; assumption }
end

section
local attribute [instance] uniform_space.separation_setoid

lemma injective_separated_pure_cauchy {α : Type*} [uniform_space α] [s : separated α] :
  function.injective (λa:α, ⟦pure_cauchy a⟧) | a b h :=
separated_def.1 s _ _ $ assume s hs,
let ⟨t, ht, hts⟩ :=
  by rw [← (@uniform_embedding_pure_cauchy α _).right, filter.mem_comap_sets] at hs; exact hs in
have (pure_cauchy a, pure_cauchy b) ∈ t, from quotient.exact h t ht,
@hts (a, b) this

end

section prod
variables {α : Type*} {β : Type*} [uniform_space α] [uniform_space β]

def prod : Cauchy α × Cauchy β → Cauchy (α × β) :=
dense_embedding.extend (dense_embedding_pure_cauchy.prod dense_embedding_pure_cauchy) pure_cauchy

lemma prod_pure_cauchy_pure_cauchy (a : α) (b :β) :
  prod (pure_cauchy a, pure_cauchy b) = pure_cauchy (a, b) :=
uniformly_extend_of_emb
  (uniform_embedding_pure_cauchy.prod uniform_embedding_pure_cauchy)
  (dense_embedding_pure_cauchy.prod dense_embedding_pure_cauchy).dense
  (a, b)

lemma uniform_continuous_prod : uniform_continuous (@prod α β _ _) :=
uniform_continuous_uniformly_extend
  (uniform_embedding_pure_cauchy.prod uniform_embedding_pure_cauchy)
  (dense_embedding_pure_cauchy.prod dense_embedding_pure_cauchy).dense
  uniform_embedding_pure_cauchy.uniform_continuous

lemma uniform_continuous₂_prod : uniform_continuous₂ (function.curry $ @prod α β _ _) :=
(uniform_continuous₂_curry _).2 uniform_continuous_prod

end prod

end Cauchy

local attribute [instance] uniform_space.separation_setoid

open Cauchy set

namespace uniform_space
variables (α : Type*) [uniform_space α]
variables {β : Type*} [uniform_space β]
variables {γ : Type*} [uniform_space γ]

/-- Hausdorff completion of `α` -/
def completion := quotient (separation_setoid $ Cauchy α)

namespace completion

@[priority 50]
instance : uniform_space (completion α) := by dunfold completion ; apply_instance

instance : complete_space (completion α) := by dunfold completion ; apply_instance

instance : separated (completion α) := by dunfold completion ; apply_instance

instance : t2_space (completion α) := separated_t2

instance : regular_space (completion α) := separated_regular

/-- Automatic coercion from `α` to its completion. Not always injective. -/
instance : has_coe α (completion α) := ⟨quotient.mk ∘ pure_cauchy⟩

protected lemma coe_eq : (coe : α → completion α) = quotient.mk ∘ pure_cauchy := rfl

lemma uniform_continuous_coe : uniform_continuous (coe : α → completion α) :=
uniform_continuous.comp uniform_embedding_pure_cauchy.uniform_continuous
  sep_quot.uniform_continuous_mk

lemma continuous_coe : continuous (coe : α → completion α) :=
uniform_continuous.continuous (uniform_continuous_coe α)

lemma comap_coe_eq_uniformity :
  uniformity.comap (λ(p:α×α), ((p.1 : completion α), (p.2 : completion α))) = uniformity :=
begin
  have : (λx:α×α, ((x.1 : completion α), (x.2 : completion α))) =
    (λx:(Cauchy α)×(Cauchy α), (⟦x.1⟧, ⟦x.2⟧)) ∘ (λx:α×α, (pure_cauchy x.1, pure_cauchy x.2)),
  { ext ⟨a, b⟩; simp; refl },
  rw [this, ← filter.comap_comap_comp, sep_quot.comap_quotient_eq_uniformity, uniform_embedding_pure_cauchy.2]
end

lemma uniform_embedding_coe [separated α] : uniform_embedding  (coe : α → completion α) :=
⟨injective_separated_pure_cauchy, comap_coe_eq_uniformity α⟩

variable {α}

lemma dense : closure (range (coe : α → completion α)) = univ :=
by rw [completion.coe_eq, range_comp]; exact quotient_dense_of_dense pure_cauchy_dense

lemma dense_embedding_coe [separated α]: dense_embedding (coe : α → completion α) :=
(uniform_embedding_coe α).dense_embedding (assume x, by rw [dense]; exact mem_univ _)

lemma dense₂ : closure (range (λx:α × β, ((x.1 : completion α), (x.2 : completion β)))) = univ :=
by rw [← set.prod_range_range_eq, closure_prod_eq, dense, dense, univ_prod_univ]

lemma dense₃ :
  closure (range (λx:α × (β × γ), ((x.1 : completion α), ((x.2.1 : completion β), (x.2.2 : completion γ))))) = univ :=
let a : α → completion α := coe, bc := λp:β × γ, ((p.1 : completion β), (p.2 : completion γ)) in
show closure (range (λx:α × (β × γ), (a x.1, bc x.2))) = univ,
begin
  rw [← set.prod_range_range_eq, @closure_prod_eq _ _ _ _ (range a) (range bc), ← univ_prod_univ],
  congr,
  exact dense,
  exact dense₂
end

@[elab_as_eliminator]
lemma induction_on {p : completion α → Prop}
  (a : completion α) (hp : is_closed {a | p a}) (ih : ∀a:α, p a) : p a :=
is_closed_property dense hp ih a

@[elab_as_eliminator]
lemma induction_on₂ {p : completion α → completion β → Prop}
  (a : completion α) (b : completion β)
  (hp : is_closed {x : completion α × completion β | p x.1 x.2})
  (ih : ∀(a:α) (b:β), p a b) : p a b :=
have ∀x : completion α × completion β, p x.1 x.2, from
  is_closed_property dense₂ hp $ assume ⟨a, b⟩, ih a b,
this (a, b)

@[elab_as_eliminator]
lemma induction_on₃ {p : completion α → completion β → completion γ → Prop}
  (a : completion α) (b : completion β) (c : completion γ)
  (hp : is_closed {x : completion α × completion β × completion γ | p x.1 x.2.1 x.2.2})
  (ih : ∀(a:α) (b:β) (c:γ), p a b c) : p a b c :=
have ∀x : completion α × completion β × completion γ, p x.1 x.2.1 x.2.2, from
  is_closed_property dense₃ hp $ assume ⟨a, b, c⟩, ih a b c,
this (a, b, c)

@[elab_as_eliminator]
lemma induction_on₄ {δ : Type*} [uniform_space δ]
  {p : completion α → completion β → completion γ → completion δ → Prop}
  (a : completion α) (b : completion β) (c : completion γ) (d : completion δ)
  (hp : is_closed {x : (completion α × completion β) × (completion γ × completion δ) | p x.1.1 x.1.2 x.2.1 x.2.2})
  (ih : ∀(a:α) (b:β) (c:γ) (d : δ), p ↑a ↑b ↑c ↑d) : p a b c d :=
let
  ab := λp:α × β, ((p.1 : completion α), (p.2 : completion β)),
  cd := λp:γ × δ, ((p.1 : completion γ), (p.2 : completion δ))
in
have dense₄ : closure (range (λx:(α × β) × (γ × δ), (ab x.1, cd x.2))) = univ,
begin
  rw [← set.prod_range_range_eq, @closure_prod_eq _ _ _ _ (range ab) (range cd), ← univ_prod_univ],
  congr,
  exact dense₂,
  exact dense₂
end,
have ∀x:(completion α × completion β) × (completion γ × completion δ), p x.1.1 x.1.2 x.2.1 x.2.2, from
  is_closed_property dense₄ hp (assume p:(α×β)×(γ×δ), ih p.1.1 p.1.2 p.2.1 p.2.2),
this ((a, b), (c, d))

lemma ext [t2_space β] {f g : completion α → β} (hf : continuous f) (hg : continuous g)
  (h : ∀a:α, f a = g a) : f = g :=
funext $ assume a, completion.induction_on a (is_closed_eq hf hg) h

section extension
variables {f : α → β}
variables [complete_space β] [separated β]

/-- "Extension" to the completion. Based on `Cauchy.extend`, which is defined for any map `f` but
returns an arbitrary constant value if `f` is not uniformly continuous -/
protected def extension (f : α → β) : completion α → β :=
quotient.lift (extend f) $ assume a b, uniform_continuous_extend.eq_of_separated

lemma uniform_continuous_extension : uniform_continuous (completion.extension f) :=
uniform_continuous_extend

lemma continuous_extension : continuous (completion.extension f) :=
uniform_continuous_extension.continuous

@[simp] lemma extension_coe (hf : uniform_continuous f) (a : α) : (completion.extension f) a = f a :=
extend_pure_cauchy hf a

end extension

section map
variables {f : α → β}

/-- Completion functor acting on morphisms -/
protected def map (f : α → β) : completion α → completion β :=
completion.extension (coe ∘ f)

lemma uniform_continuous_map : uniform_continuous (completion.map f) :=
uniform_continuous_extend

lemma continuous_map : continuous (completion.map f) :=
uniform_continuous_extension.continuous

@[simp] lemma map_coe (hf : uniform_continuous f) (a : α) : (completion.map f) a = f a :=
by rw [completion.map, extension_coe]; from hf.comp (uniform_continuous_coe β)

lemma map_unique {f : α → β} {g : completion α → completion β}
  (hg : uniform_continuous g) (h : ∀a:α, ↑(f a) = g a) : completion.map f = g :=
completion.ext continuous_map hg.continuous $
begin
  intro a,
  simp only [completion.map, (∘), h],
  rw [extension_coe ((uniform_continuous_coe α).comp hg)]
end

lemma map_id : completion.map (@id α) = id :=
map_unique uniform_continuous_id (assume a, rfl)

lemma extension_map [complete_space γ] [separated γ] {f : β → γ} {g : α → β}
  (hf : uniform_continuous f) (hg : uniform_continuous g) :
  completion.extension f ∘ completion.map g = completion.extension (f ∘ g) :=
completion.ext (continuous_map.comp continuous_extension) continuous_extension $
  by intro a; simp only [hg, hf, hg.comp hf, (∘), map_coe, extension_coe]

lemma map_comp {f : α → β} {g : β → γ} (hf : uniform_continuous f) (hg : uniform_continuous g) :
  completion.map g ∘ completion.map f = completion.map (g ∘ f) :=
extension_map (hg.comp (uniform_continuous_coe _)) hf

end map

/- In this section we construct isomorphisms between the completion of a uniform space and the
completion of its separation quotient -/
section sep_quot_completion

def completion_sep_quot_equiv (α : Type u) [uniform_space α] :
  completion (sep_quot α) ≃ completion α :=
begin
  refine ⟨completion.extension (sep_quot.lift (coe : α → completion α)),
    completion.map quotient.mk, _, _⟩,
  { assume a,
    refine completion.induction_on a (is_closed_eq (continuous_extension.comp continuous_map) continuous_id) _,
    rintros ⟨a⟩,
    show completion.map quotient.mk (completion.extension (sep_quot.lift coe) ↑⟦a⟧) = ↑⟦a⟧,
    rw [extension_coe (sep_quot.uniform_continuous_lift $ uniform_continuous_coe α),
      sep_quot.lift_mk (uniform_continuous_coe α).separated_map,
      completion.map_coe sep_quot.uniform_continuous_mk], },
  { assume a,
    refine completion.induction_on a (is_closed_eq (continuous_map.comp continuous_extension) continuous_id) _,
    assume a,
    rw [map_coe sep_quot.uniform_continuous_mk,
      extension_coe (sep_quot.uniform_continuous_lift $ uniform_continuous_coe α),
      sep_quot.lift_mk (uniform_continuous_coe α).separated_map _] }
end

lemma uniform_continuous_completion_sep_quot_equiv :
  uniform_continuous (completion_sep_quot_equiv α) :=
uniform_continuous_extension

lemma uniform_continuous_completion_sep_quot_equiv_symm :
  uniform_continuous (completion_sep_quot_equiv α).symm :=
uniform_continuous_map

end sep_quot_completion

section prod
variables [uniform_space β]
protected def prod {α β} [uniform_space α] [uniform_space β] : completion α → completion β → completion (α × β) :=
sep_quot.lift₂ (λ a b, ⟦Cauchy.prod (a, b)⟧)

lemma uniform_continuous_prod : uniform_continuous₂ (@completion.prod α β _ _) :=
sep_quot.uniform_continuous_lift₂ $ uniform_continuous₂_prod.comp sep_quot.uniform_continuous_mk

lemma prod_coe_coe (a : α) (b : β) :
  completion.prod (a : completion α) (b : completion β) = (a, b) :=
begin
  change sep_quot.lift₂ (λ (a : Cauchy α) (b : Cauchy β), ⟦Cauchy.prod (a, b)⟧) ⟦pure_cauchy a⟧ ⟦pure_cauchy b⟧ = ⟦pure_cauchy (a, b)⟧,
  rw ←Cauchy.prod_pure_cauchy_pure_cauchy,
  apply sep_quot.lift₂_mk_mk (uniform_continuous₂_prod.comp sep_quot.uniform_continuous_mk).separated_map
end
end prod

section map₂

protected def map₂ (f : α → β → γ) (a : completion α) (b : completion β) : completion γ :=
completion.map (λp:α×β, f p.1 p.2) (completion.prod  a b)

lemma uniform_continuous_map₂' (f : α → β → γ) :
  uniform_continuous₂ (completion.map₂ f) :=
uniform_continuous_prod.comp completion.uniform_continuous_map

lemma continuous_map₂ {δ} [topological_space δ] {f : α → β → γ}
  {a : δ → completion α} {b : δ → completion β} (ha : continuous a) (hb : continuous b) :
  continuous (λd:δ, completion.map₂ f (a d) (b d)) :=
(continuous.prod_mk ha hb).comp (uniform_continuous_map₂' f).continuous

lemma map₂_coe_coe (a : α) (b : β) (f : α → β → γ) (hf : uniform_continuous (λp:α×β, f p.1 p.2)) :
  completion.map₂ f (a : completion α) (b : completion β) = f a b :=
by rw [completion.map₂, completion.prod_coe_coe, completion.map_coe hf]

end map₂

section group

instance [has_zero α] : has_zero (completion α) := ⟨(0 : α)⟩
instance [has_neg α] : has_neg (completion α) := ⟨completion.map (λa, -a : α → α)⟩
instance [has_add α] : has_add (completion α) := ⟨completion.map₂ (+)⟩

lemma coe_zero [has_zero α] : ((0 : α) : completion α) = 0 := rfl

section uniform_add_group
variables [add_group α] [uniform_add_group α]

lemma coe_neg (a : α) : ((- a : α) : completion α) = - a :=
(map_coe uniform_continuous_neg' a).symm

lemma coe_add (a b : α) : ((a + b : α) : completion α) = a + b :=
(map₂_coe_coe a b (+) uniform_continuous_add').symm

instance : add_group (completion α) :=
{ zero_add     := assume a, completion.induction_on a
    (is_closed_eq (continuous_map₂ continuous_const continuous_id) continuous_id)
    (assume a, show 0 + (a : completion α) = a, by rw [← coe_zero, ← coe_add, zero_add]),
  add_zero     := assume a, completion.induction_on a
    (is_closed_eq (continuous_map₂ continuous_id continuous_const) continuous_id)
    (assume a, show (a : completion α) + 0 = a, by rw [← coe_zero, ← coe_add, add_zero]),
  add_left_neg := assume a, completion.induction_on a
    (is_closed_eq (continuous_map₂ completion.continuous_map continuous_id) continuous_const)
    (assume a, show - (a : completion α) + a = 0, by rw [← coe_neg, ← coe_add, add_left_neg, coe_zero]),
  add_assoc    := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous_map₂
        (continuous_map₂ continuous_fst (continuous_snd.comp continuous_fst)) (continuous_snd.comp continuous_snd))
      (continuous_map₂ continuous_fst
        (continuous_map₂ (continuous_snd.comp continuous_fst) (continuous_snd.comp continuous_snd))))
    (assume a b c, show (a : completion α) + b + c = a + (b + c),
      by repeat { rw [← coe_add] }; rw [add_assoc]),
  .. completion.has_zero, .. completion.has_neg, ..completion.has_add }

instance : uniform_add_group (completion α) :=
⟨ (uniform_continuous.prod_mk uniform_continuous_fst
  (uniform_continuous_snd.comp uniform_continuous_map)).comp (uniform_continuous_map₂' (+))  ⟩

instance is_add_group_hom_coe : is_add_group_hom (coe : α → completion α) :=
⟨ coe_add ⟩

lemma is_add_group_hom_extension [add_group β] [uniform_add_group β] [complete_space β] [separated β]
  {f : α → β} [is_add_group_hom f] (hf : continuous f) : is_add_group_hom (completion.extension f) :=
have hf : uniform_continuous f, from uniform_continuous_of_continuous hf,
⟨assume a b, completion.induction_on₂ a b
  (is_closed_eq
    (continuous_add'.comp continuous_extension)
    (continuous_add (continuous_fst.comp continuous_extension) (continuous_snd.comp continuous_extension)))
  (assume a b, by rw [← coe_add, extension_coe hf, extension_coe hf, extension_coe hf, is_add_group_hom.add f])⟩

lemma is_add_group_hom_map [add_group β] [uniform_add_group β]
  {f : α → β} [is_add_group_hom f] (hf : continuous f) : is_add_group_hom (completion.map f) :=
is_add_group_hom_extension (hf.comp (continuous_coe _))

section instance_max_depth
-- TODO: continuous_add requires some long proofs through
-- uniform_add_group / topological_add_group w.r.t prod / completion etc
set_option class.instance_max_depth 52
-- set_option trace.class_instances true

lemma is_add_group_hom_prod [add_group β] [uniform_add_group β] :
  is_add_group_hom (function.uncurry $ @completion.prod α β _ _) :=
⟨assume ⟨a₁, a₂⟩ ⟨b₁, b₂⟩,
  begin
    refine completion.induction_on₄ a₁ a₂ b₁ b₂ (is_closed_eq _ _) _,
    { refine continuous.comp _ uniform_continuous_prod.continuous,
      refine continuous_add _ _,
      exact continuous.prod_mk (continuous_fst.comp continuous_fst) (continuous_fst.comp continuous_snd),
      exact continuous.prod_mk (continuous_snd.comp continuous_fst) (continuous_snd.comp continuous_snd) },
    { refine continuous_add _ _,
      refine continuous.comp _ uniform_continuous_prod.continuous,
      exact continuous.prod_mk (continuous_fst.comp continuous_fst) (continuous_fst.comp continuous_snd),
      refine continuous.comp _ uniform_continuous_prod.continuous,
      exact continuous.prod_mk (continuous_snd.comp continuous_fst) (continuous_snd.comp continuous_snd) },
    { assume a b c d,
      show completion.prod (↑a + ↑c) (↑b + ↑d) = (completion.prod ↑a ↑b) + (completion.prod ↑c ↑d),
      rw [← coe_add, ← coe_add, prod_coe_coe, prod_coe_coe, prod_coe_coe, ← coe_add],
      refl }
  end⟩

end instance_max_depth

end uniform_add_group

instance [add_comm_group α] [uniform_add_group α] : add_comm_group (completion α) :=
{ add_comm  := assume a b, completion.induction_on₂ a b
    (is_closed_eq (continuous_map₂ continuous_fst continuous_snd) (continuous_map₂ continuous_snd continuous_fst))
    (assume a b, by rw [← coe_add, ← coe_add, add_comm]),
  .. completion.add_group }

end group

end completion

end uniform_space

namespace add_comm_group
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
variables [add_comm_group α] [add_comm_group β] [add_comm_group γ]

/- TODO: when modules are changed to have more explicit base ring, then change replace `is_Z_bilin`
by using `is_bilinear_map ℤ` from `tensor_product`. -/
class is_Z_bilin (f : α × β → γ) : Prop :=
(add_left  : ∀ a a' b, f (a + a', b) = f (a, b) + f (a', b))
(add_right : ∀ a b b', f (a, b + b') = f (a, b) + f (a, b'))

variables (f : α × β → γ) [is_Z_bilin f]

instance is_Z_bilin.comp_hom {g : γ → δ} [add_comm_group δ] [is_add_group_hom g] :
  is_Z_bilin (g ∘ f) :=
by constructor; simp [(∘), is_Z_bilin.add_left f, is_Z_bilin.add_right f, is_add_group_hom.add g]

instance is_Z_bilin.comp_swap : is_Z_bilin (f ∘ prod.swap) :=
⟨λ a a' b, is_Z_bilin.add_right f b a a',
 λ a b b', is_Z_bilin.add_left f b b' a⟩

lemma is_Z_bilin.zero_left : ∀ b, f (0, b) = 0 :=
begin
  intro b,
  apply add_self_iff_eq_zero.1,
  rw ←is_Z_bilin.add_left f,
  simp
end

lemma is_Z_bilin.zero_right : ∀ a, f (a, 0) = 0 :=
is_Z_bilin.zero_left (f ∘ prod.swap)

lemma is_Z_bilin.zero : f (0, 0) = 0 :=
is_Z_bilin.zero_left f 0

lemma is_Z_bilin.neg_left  : ∀ a b, f (-a, b) = -f (a, b) :=
begin
  intros a b,
  apply eq_of_sub_eq_zero,
  rw [sub_eq_add_neg, neg_neg, ←is_Z_bilin.add_left f, neg_add_self, is_Z_bilin.zero_left f]
end

lemma is_Z_bilin.neg_right  : ∀ a b, f (a, -b) = -f (a, b) :=
assume a b, is_Z_bilin.neg_left (f ∘ prod.swap) b a

lemma is_Z_bilin.sub_left : ∀ a a' b, f (a - a', b) = f (a, b) - f (a', b) :=
begin
  intros,
  dsimp [algebra.sub],
  rw [is_Z_bilin.add_left f, is_Z_bilin.neg_left f]
end

lemma is_Z_bilin.sub_right : ∀ a b b', f (a, b - b') = f (a, b) - f (a,b') :=
assume a b b', is_Z_bilin.sub_left (f ∘ prod.swap) b b' a
end add_comm_group

open add_comm_group filter set function

section
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

-- α, β and G are abelian topological groups, G is complete Hausdorff
variables [topological_space α] [add_comm_group α] [topological_add_group α]
variables [topological_space β] [add_comm_group β] [topological_add_group β]
variables {G : Type*} [uniform_space G] [add_comm_group G] [uniform_add_group G]
  [complete_space G] [separated G]

variables {ψ : α × β → G} (hψ : continuous ψ) [ψbilin : is_Z_bilin ψ]

include hψ ψbilin

lemma is_Z_bilin.tendsto_zero_left (x₁ : α) : tendsto ψ (nhds (x₁, 0)) (nhds 0) :=
begin
  have := continuous.tendsto hψ (x₁, 0),
  rwa [is_Z_bilin.zero_right ψ] at this
end

lemma is_Z_bilin.tendsto_zero_right (y₁ : β) : tendsto ψ (nhds (0, y₁)) (nhds 0) :=
begin
  have := continuous.tendsto hψ (0, y₁),
  rwa [is_Z_bilin.zero_left ψ] at this
end
end

section
variables {α : Type u} {β : Type v}
variables [topological_space α] [add_comm_group α] [topological_add_group α]

-- β is a dense subgroup of α, inclusion is denoted by e
variables [topological_space β] [add_comm_group β] [topological_add_group β]
variables {e : β → α} [is_add_group_hom e] (de : dense_embedding e)
include de

lemma tendsto_sub_comap_self (x₀ : α) :
  tendsto (λt:β×β, t.2 - t.1) (comap (λp:β×β, (e p.1, e p.2)) $ nhds (x₀, x₀)) (nhds 0) :=
begin
  have comm : (λx:α×α, x.2-x.1) ∘ (λt:β×β, (e t.1, e t.2)) = e ∘ (λt:β×β, t.2 - t.1),
  { ext t,
    change e t.2 - e t.1 = e (t.2 - t.1),
    rwa ← is_add_group_hom.sub e t.2 t.1 },
  have lim : tendsto (λ x : α × α, x.2-x.1) (nhds (x₀, x₀)) (nhds (e 0)),
    { have := continuous.tendsto (continuous.comp continuous_swap continuous_sub') (x₀, x₀),
      simpa [-sub_eq_add_neg, sub_self, eq.symm (is_add_group_hom.zero e)] using this },
  have := de.tendsto_comap_nhds_nhds lim comm,
  simp [-sub_eq_add_neg, this]
end
end


namespace dense_embedding
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
variables {G : Type*}

-- β is a dense subgroup of α, inclusion is denoted by e
-- δ is a dense subgroup of γ, inclusion is denoted by f
variables [topological_space α] [add_comm_group α] [topological_add_group α]
variables [topological_space β] [add_comm_group β] [topological_add_group β]
variables [topological_space γ] [add_comm_group γ] [topological_add_group γ]
variables [topological_space δ] [add_comm_group δ] [topological_add_group δ]
variables [uniform_space G] [add_comm_group G] [uniform_add_group G] [separated G] [complete_space G]
variables {e : β → α} [is_add_group_hom e] (de : dense_embedding e)
variables {f : δ → γ} [is_add_group_hom f] (df : dense_embedding f)
variables {φ : β × δ → G} (hφ : continuous φ) [bilin : is_Z_bilin φ]

include de df hφ bilin

variables {W' : set G} (W'_nhd : W' ∈ (nhds (0 : G)).sets)
include W'_nhd

private lemma extend_Z_bilin_aux (x₀ : α) (y₁ : δ) :
  ∃ U₂ ∈ (comap e (nhds x₀)).sets, ∀ x x' ∈ U₂, φ (x' - x, y₁) ∈ W' :=
begin
  let Nx := nhds x₀,
  let ee := λ u : β × β, (e u.1, e u.2),

  have lim1 : tendsto (λ a : β × β, (a.2 - a.1, y₁)) (filter.prod (comap e Nx) (comap e Nx)) (nhds (0, y₁)),
  { have := tendsto.prod_mk (tendsto_sub_comap_self de x₀) (tendsto_const_nhds : tendsto (λ (p : β × β), y₁) (comap ee $ nhds (x₀, x₀)) (nhds y₁)),
    rw [nhds_prod_eq, prod_comap_comap_eq, ←nhds_prod_eq],
    exact (this : _) },

  have lim := tendsto.comp lim1 (is_Z_bilin.tendsto_zero_right hφ y₁),
  rw tendsto_prod_self_iff at lim,
  exact lim W' W'_nhd,
end

private lemma extend_Z_bilin_key (x₀ : α) (y₀ : γ) :
  ∃ U ∈ (comap e (nhds x₀)).sets, ∃ V ∈ (comap f (nhds y₀)).sets,
    ∀ x x' ∈ U, ∀ y y' ∈ V, φ (x', y') - φ (x, y) ∈ W' :=
begin
  let Nx := nhds x₀,
  let Ny := nhds y₀,
  let dp := dense_embedding.prod de df,
  let ee := λ u : β × β, (e u.1, e u.2),
  let ff := λ u : δ × δ, (f u.1, f u.2),

  have lim_φ : filter.tendsto φ (nhds (0, 0)) (nhds 0),
  { have := continuous.tendsto hφ (0, 0),
    rwa [is_Z_bilin.zero φ] at this },

  have lim_φ_sub_sub : tendsto (λ (p : (β × β) × (δ × δ)), φ (p.1.2 - p.1.1, p.2.2 - p.2.1))
    (filter.prod (comap ee $ nhds (x₀, x₀)) (comap ff $ nhds (y₀, y₀))) (nhds 0),
  { have lim_sub_sub :  tendsto (λ (p : (β × β) × δ × δ), (p.1.2 - p.1.1, p.2.2 - p.2.1))
      (filter.prod (comap ee (nhds (x₀, x₀))) (comap ff (nhds (y₀, y₀)))) (filter.prod (nhds 0) (nhds 0)),
    { have := filter.prod_mono (tendsto_sub_comap_self de x₀) (tendsto_sub_comap_self df y₀),
      rwa prod_map_map_eq at this },
    rw ← nhds_prod_eq at lim_sub_sub,
    exact tendsto.comp lim_sub_sub lim_φ },

  rcases exists_nhds_quarter W'_nhd with ⟨W, W_nhd, W4⟩,

  have : ∃ U₁ ∈ (comap e (nhds x₀)).sets, ∃ V₁ ∈ (comap f (nhds y₀)).sets,
    ∀ x x' ∈ U₁, ∀ y y' ∈ V₁,  φ (x'-x, y'-y) ∈ W,
  { have := tendsto_prod_iff.1 lim_φ_sub_sub W W_nhd,
    repeat { rw [nhds_prod_eq, ←prod_comap_comap_eq] at this },
    rcases this with ⟨U, U_in, V, V_in, H⟩,
    rw [mem_prod_same_iff] at U_in V_in,
    rcases U_in with ⟨U₁, U₁_in, HU₁⟩,
    rcases V_in with ⟨V₁, V₁_in, HV₁⟩,
    existsi [U₁, U₁_in, V₁, V₁_in],
    intros x x' x_in x'_in y y' y_in y'_in,
    exact H _ _ (HU₁ (mk_mem_prod x_in x'_in)) (HV₁ (mk_mem_prod y_in y'_in)) },
  rcases this with ⟨U₁, U₁_nhd, V₁, V₁_nhd, H⟩,

  have : ∃ x₁, x₁ ∈ U₁ := exists_mem_of_ne_empty
    (forall_sets_neq_empty_iff_neq_bot.2 de.comap_nhds_neq_bot U₁ U₁_nhd),
  rcases this with ⟨x₁, x₁_in⟩,

  have : ∃ y₁, y₁ ∈ V₁ := exists_mem_of_ne_empty
    (forall_sets_neq_empty_iff_neq_bot.2 df.comap_nhds_neq_bot V₁ V₁_nhd),
  rcases this with ⟨y₁, y₁_in⟩,

  rcases (extend_Z_bilin_aux de df hφ W_nhd x₀ y₁) with ⟨U₂, U₂_nhd, HU⟩,
  rcases (extend_Z_bilin_aux df de (continuous.comp continuous_swap hφ) W_nhd y₀ x₁) with ⟨V₂, V₂_nhd, HV⟩,

  existsi [U₁ ∩ U₂, inter_mem_sets U₁_nhd U₂_nhd,
            V₁ ∩ V₂, inter_mem_sets V₁_nhd V₂_nhd],

  rintros x x' ⟨xU₁, xU₂⟩ ⟨x'U₁, x'U₂⟩ y y' ⟨yV₁, yV₂⟩ ⟨y'V₁, y'V₂⟩,
  have key_formula : φ(x', y') - φ(x, y) = φ(x' - x, y₁) + φ(x' - x, y' - y₁) + φ(x₁, y' - y) + φ(x - x₁, y' - y),
  { repeat { rw is_Z_bilin.sub_left φ },
    repeat { rw is_Z_bilin.sub_right φ },
    apply eq_of_sub_eq_zero,
    simp },
  rw key_formula,
  have h₁ := HU x x' xU₂ x'U₂,
  have h₂ := H x x' xU₁ x'U₁ y₁ y' y₁_in y'V₁,
  have h₃ := HV y y' yV₂ y'V₂,
  have h₄ := H x₁ x x₁_in xU₁ y y' yV₁ y'V₁,

  exact W4 h₁ h₂ h₃ h₄
end
omit W'_nhd

/-- Bourbaki GT III.6.5 Theorem I:
ℤ-bilinear continuous maps from dense sub-groups into a complete Hausdorff group extend by continuity.
Note: Bourbaki assumes that α and β are also complete Hausdorff, but this is not necessary. -/
theorem extend_Z_bilin  : continuous (extend (dense_embedding.prod de df) φ) :=
begin
  let dp := dense_embedding.prod de df,
  refine dense_embedding.continuous_extend_of_cauchy (dense_embedding.prod de df) _,
  rintro ⟨x₀, y₀⟩,
  split,
  { apply map_ne_bot,
    apply comap_neq_bot,

    intros U h,
    rcases exists_mem_of_ne_empty (mem_closure_iff_nhds.1 (dp.dense (x₀, y₀)) U h)
      with ⟨x, x_in, ⟨z, z_x⟩⟩,
    existsi z,
    cc },
  { suffices : map (λ (p : (β × δ) × (β × δ)), φ p.2 - φ p.1)
      (comap (λ (p : (β × δ) × β × δ), ((e p.1.1, f p.1.2), (e p.2.1, f p.2.2)))
         (filter.prod (nhds (x₀, y₀)) (nhds (x₀, y₀)))) ≤ nhds 0,
    by rwa [uniformity_eq_right_uniformity G, prod_map_map_eq, ←map_le_iff_le_comap, filter.map_map,
        prod_comap_comap_eq],

    intros W' W'_nhd,

    have key := extend_Z_bilin_key de df hφ W'_nhd x₀ y₀,
    rcases key with ⟨U, U_nhd, V, V_nhd, h⟩,
    rw mem_comap_sets at U_nhd,
    rcases U_nhd with ⟨U', U'_nhd, U'_sub⟩,
    rw mem_comap_sets at V_nhd,
    rcases V_nhd with ⟨V', V'_nhd, V'_sub⟩,

    rw [mem_map, mem_comap_sets, nhds_prod_eq],
    existsi set.prod (set.prod U' V') (set.prod U' V'),
    rw mem_prod_same_iff,

    simp only [exists_prop],
    split,
    { have := prod_mem_prod U'_nhd V'_nhd,
      tauto },
    { intros p h',
      simp only [set.mem_preimage_eq, set.prod_mk_mem_set_prod_eq] at h',
      rcases p with ⟨⟨x, y⟩, ⟨x', y'⟩⟩,
      apply h ; tauto } }
end
end dense_embedding

namespace uniform_space.completion
open dense_embedding uniform_space
variables (α : Type u) [ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] [separated α]

instance is_Z_bilin_mul : is_Z_bilin (λp:α×α, p.1 * p.2) :=
⟨assume a a' b, add_mul a a' b, assume a b b', mul_add a b b'⟩

instance : has_one (completion α) := ⟨(1:α)⟩

instance : has_mul (completion α) :=
⟨λa b, extend (dense_embedding_coe.prod dense_embedding_coe)
  ((coe : α → completion α) ∘ (λp:α×α, p.1 * p.2)) (a, b)⟩

lemma coe_one : ((1 : α) : completion α) = 1 := rfl

lemma continuous_mul' : continuous (λp:completion α×completion α, p.1 * p.2) :=
suffices continuous $ extend (dense_embedding_coe.prod dense_embedding_coe) $
  ((coe : α → completion α) ∘ (λp:α×α, p.1 * p.2)),
{ convert this, ext ⟨a, b⟩, refl },
extend_Z_bilin dense_embedding_coe dense_embedding_coe (continuous.comp continuous_mul' (continuous_coe α))

section rules
variables {α}
lemma coe_mul (a b : α) : ((a * b : α) : completion α) = a * b :=
eq.symm (extend_e_eq (dense_embedding_coe.prod dense_embedding_coe) (a, b))

lemma continuous_mul {β : Type v} [topological_space β] {f g : β → completion α}
  (hf : continuous f) (hg : continuous g) : continuous (λb, f b * g b) :=
(continuous.prod_mk hf hg).comp (continuous_mul' α)
end rules

instance : ring (completion α) :=
{ one_mul       := assume a, completion.induction_on a
    (is_closed_eq (continuous_mul continuous_const continuous_id) continuous_id)
    (assume a, by rw [← coe_one, ← coe_mul, one_mul]),
  mul_one       := assume a, completion.induction_on a
    (is_closed_eq (continuous_mul continuous_id continuous_const) continuous_id)
    (assume a, by rw [← coe_one, ← coe_mul, mul_one]),
  mul_assoc     := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous_mul (continuous_mul continuous_fst (continuous_snd.comp continuous_fst))
        (continuous_snd.comp continuous_snd))
      (continuous_mul continuous_fst
        (continuous_mul (continuous_snd.comp continuous_fst) (continuous_snd.comp continuous_snd))))
    (assume a b c, by rw [← coe_mul, ← coe_mul, ← coe_mul, ← coe_mul, mul_assoc]),
  left_distrib  := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous_mul continuous_fst (continuous_add
        (continuous_snd.comp continuous_fst)
        (continuous_snd.comp continuous_snd)))
      (continuous_add
        (continuous_mul continuous_fst (continuous_snd.comp continuous_fst))
        (continuous_mul continuous_fst (continuous_snd.comp continuous_snd))))
    (assume a b c, by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ←coe_add, mul_add]),
  right_distrib := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous_mul (continuous_add continuous_fst
        (continuous_snd.comp continuous_fst)) (continuous_snd.comp continuous_snd))
      (continuous_add
        (continuous_mul continuous_fst (continuous_snd.comp continuous_snd))
        (continuous_mul (continuous_snd.comp continuous_fst) (continuous_snd.comp continuous_snd))))
    (assume a b c, by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ←coe_add, add_mul]),
  ..completion.add_comm_group, ..completion.has_mul α, ..completion.has_one α }

instance top_ring_compl : topological_ring (completion α) :=
{ continuous_add := continuous_add',
  continuous_mul := uniform_space.completion.continuous_mul' α,
  continuous_neg := continuous_neg' }

instance is_ring_hom_coe : is_ring_hom (coe : α → completion α) :=
⟨coe_one α, assume a b, coe_mul a b, assume a b, coe_add a b⟩

instance is_ring_hom_extension
  {β : Type v} [uniform_space β] [ring β] [uniform_add_group β] [topological_ring β]
    [complete_space β] [separated β]
  {f : α → β} [is_ring_hom f] (hf : continuous f) :
  is_ring_hom (completion.extension f) :=
have hf : uniform_continuous f, from uniform_continuous_of_continuous hf,
{ map_one := by rw [← coe_one, extension_coe hf, is_ring_hom.map_one f],
  map_add := assume a b, completion.induction_on₂ a b
    (is_closed_eq
      (continuous_add'.comp continuous_extension)
      (continuous_add (continuous_fst.comp continuous_extension) (continuous_snd.comp continuous_extension)))
    (assume a b,
      by rw [← coe_add, extension_coe hf, extension_coe hf, extension_coe hf, is_add_group_hom.add f]),
  map_mul := assume a b, completion.induction_on₂ a b
    (is_closed_eq
      ((continuous_mul' α).comp continuous_extension)
      (_root_.continuous_mul (continuous_fst.comp continuous_extension) (continuous_snd.comp continuous_extension)))
    (assume a b,
      by rw [← coe_mul, extension_coe hf, extension_coe hf, extension_coe hf, is_ring_hom.map_mul f]) }

instance is_ring_hom_map 
  {β : Type v} [uniform_space β] [ring β] [uniform_add_group β] [topological_ring β]
    [separated β]
  {f : α → β} [is_ring_hom f] (hf : continuous f) :
  is_ring_hom (completion.map f) :=
completion.is_ring_hom_extension α (hf.comp (continuous_coe β))

end uniform_space.completion

section hcompletion
open uniform_space

variables (α : Type*)  [uniform_space α] 

def hcompletion := completion (sep_quot α)

local attribute [instance] separation_setoid
instance : has_coe α (hcompletion α) := ⟨quotient.mk ∘ Cauchy.pure_cauchy ∘ quotient.mk⟩

instance : uniform_space (hcompletion α) :=
by dunfold hcompletion ; apply_instance

instance : separated (hcompletion α) :=
by dunfold hcompletion ; apply_instance

variables {α} {β : Type*}  [uniform_space β] 

def hcompletion.extension [separated β] [complete_space β] (f : α → β) : hcompletion α → β :=
completion.extension $ sep_quot.lift f


lemma hcompletion.extension_coe [separated β] [complete_space β] {f : α → β} (hf : uniform_continuous f) (a : α) :
  (hcompletion.extension f) a = f a :=
begin
  convert completion.extension_coe (sep_quot.uniform_continuous_lift hf) _,
  rw sep_quot.lift_mk hf.separated_map,
end

def hcompletion.map (f : α → β) : hcompletion α → hcompletion β := completion.map $ sep_quot.map f
end hcompletion

section ring_hcompletion
open uniform_space
variables (α : Type*) [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] 
variables (β : Type*) [comm_ring β] [uniform_space β] [uniform_add_group β] [topological_ring β]

instance : ring (hcompletion α) :=
by dunfold hcompletion ; apply_instance

instance : topological_ring (hcompletion α) :=
by dunfold hcompletion ; apply_instance

variables {f : α → β} [is_ring_hom f] (hf : continuous f)
include hf

lemma hcompletion.extension_is_ring_hom [separated β] [complete_space β] :
  is_ring_hom (hcompletion.extension f) :=
by haveI := sep_quot.is_ring_hom_lift hf ; 
  exact uniform_space.completion.is_ring_hom_extension (sep_quot α) (sep_quot.continuous_lift hf)

lemma hcompletion.map_is_ring_hom : is_ring_hom (hcompletion.map f) :=
by haveI := sep_quot.is_ring_hom_map hf ;
  exact uniform_space.completion.is_ring_hom_map (sep_quot α) (sep_quot.continuous_map hf)
end ring_hcompletion