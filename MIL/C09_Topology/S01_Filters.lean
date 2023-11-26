import MIL.Common
import Mathlib.Topology.Instances.Real

open Set Filter Topology

def principal {α : Type*} (s : Set α) : Filter α
    where
  sets := { t | s ⊆ t }
  univ_sets := by
    have : s ⊆ univ := by
      simp
    apply this
  sets_of_superset := by
    intro x y x_in_set x_subset_y
    have : s ⊆ x := by apply x_in_set
    have : s ⊆ y := by
      apply Subset.trans this x_subset_y
    apply this
  inter_sets := by
    intro x y x_in_set y_in_set
    have : s ⊆ x := by apply x_in_set
    have : s ⊆ y := by apply y_in_set
    have : s ⊆ x ∩ y := by
      simp; constructor <;> assumption
    apply this


example : Filter ℕ where
    sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
    univ_sets := by simp
    sets_of_superset := by
      intro x y x_in_set x_subset_y
      simp
      rcases x_in_set with ⟨ N, h ⟩
      use N
      intro b
      intro g
      apply x_subset_y
      apply h
      apply g
    inter_sets := by
      intro x₁ x₂ x₁_in_set x₂_in_set
      simp
      rcases x₁_in_set with ⟨ N₁ , h₁  ⟩
      rcases x₂_in_set with ⟨ N₂  , h₂  ⟩
      use N₁+N₂
      intro b
      intro h
      constructor
      · apply h₁
        linarith
      · apply h₂
        linarith

def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  ∀ V ∈ G, f ⁻¹' V ∈ F

def Tendsto₂ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto₂ f F G ↔ Tendsto₁ f F G :=
  Iff.rfl

#check (@Filter.map_mono : ∀ {α β} {m : α → β}, Monotone (map m))

#check
  (@Filter.map_map :
    ∀ {α β γ} {f : Filter α} {m : α → β} {m' : β → γ}, map m' (map m f) = map (m' ∘ m) f)

example
  {X Y Z : Type*}
  {F : Filter X} {G : Filter Y} {H : Filter Z}
  {f : X → Y} {g : Y → Z}
  (hf : Tendsto₂  f F G) (hg : Tendsto₂  g G H) : Tendsto₂  (g ∘ f) F H
:= by
  rw [Tendsto₂]
  have : map (g ∘ f) F = map g (map f F) := by
    apply @Filter.map_map
  rw [this]
  have : map g (map f F) ≤ map g G := by
    apply @Filter.map_mono
    apply hf
  apply le_trans this hg


variable (f : ℝ → ℝ) (x₀ y₀ : ℝ)

#check comap ((↑) : ℚ → ℝ) (𝓝 x₀)

#check Tendsto (f ∘ (↑)) (comap ((↑) : ℚ → ℝ) (𝓝 x₀)) (𝓝 y₀)

section
variable {α β γ : Type*} (F : Filter α) {m : γ → β} {n : β → α}

#check (comap_comap : comap m (comap n F) = comap (n ∘ m) F)

end

example : 𝓝 (x₀, y₀) = 𝓝 x₀ ×ˢ 𝓝 y₀ :=
  nhds_prod_eq

#check le_inf_iff

example
  (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
  Tendsto f atTop (𝓝 (x₀, y₀)) ↔
  Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀)
:= by
  rw [nhds_prod_eq]
  repeat rw [Tendsto]
  repeat rw [← map_map]
  constructor
  · intro h
    constructor
    · have : map Prod.fst (map f atTop) ≤ map Prod.fst (𝓝 x₀ ×ˢ 𝓝 y₀) := by
        apply @Filter.map_mono
        apply h
      apply le_trans this
      simp
    · have : map Prod.snd (map f atTop) ≤ map Prod.snd (𝓝 x₀ ×ˢ 𝓝 y₀) := by
        apply @Filter.map_mono
        apply h
      apply le_trans this
      simp
  · intro h
    sorry





example (x₀ : ℝ) : HasBasis (𝓝 x₀) (fun ε : ℝ ↦ 0 < ε) fun ε ↦ Ioo (x₀ - ε) (x₀ + ε) :=
  nhds_basis_Ioo_pos x₀

example (u : ℕ → ℝ) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x₀)]
  simp

example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ

example (u v : ℕ → ℝ) (h : ∀ᶠ n in atTop, u n = v n) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

example (u v : ℕ → ℝ) (h : u =ᶠ[atTop] v) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

#check eventually_of_forall
#check Eventually.mono
#check Eventually.and

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  apply (hP.and (hQ.and hR)).mono
  rintro n ⟨h, h', h''⟩
  exact h'' ⟨h, h'⟩

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  filter_upwards [hP, hQ, hR] with n h h' h''
  exact h'' ⟨h, h'⟩

#check mem_closure_iff_clusterPt
#check le_principal_iff
#check neBot_of_le

example
  (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ)
  (hux : Tendsto u atTop (𝓝 x))
  (huM : ∀ᶠ n in atTop, u n ∈ M) :
  x ∈ closure M
:= by
  rw [mem_closure_iff_clusterPt]
  sorry
