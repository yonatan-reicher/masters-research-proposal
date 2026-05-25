import Mathlib.Tactic

noncomputable section
open Classical Finset

variable {n m : ℕ}

-- Definition of domino tiling

@[ext]
structure Point where
  x : ℕ
  y : ℕ
deriving Repr

inductive Domino
| H (lft : Point)
| V (top : Point)
deriving Repr

def cells : Domino → Finset Point
| Domino.H lft => { ⟨lft.x, lft.y⟩, ⟨lft.x + 1, lft.y⟩ }
| Domino.V top => { ⟨top.x, top.y⟩, ⟨top.x, top.y + 1⟩ }

def board (n m : ℕ) : Finset Point :=
  map ⟨fun xy => ⟨xy.1, xy.2⟩, by simp [Function.Injective]⟩
    (range n ×ˢ range m)

structure DominoTiling (n m : ℕ) where
  tiles : Finset Domino
  disjoint : Set.PairwiseDisjoint tiles (cells ·)
  union : tiles.disjiUnion (cells ·) disjoint = board n m

-- Lemmas about cardinalities

lemma card_domino (domino : Domino) : #(cells domino) = 2 := by
  cases domino
  case H lft => simp [cells]
  case V top => simp [cells]

lemma card_board : #(board n m) = n * m := by
  simp [board]

lemma card_tiling (tiling : DominoTiling n m) :
  2 * #tiling.tiles = n * m := by
  have := tiling.tiles.card_disjiUnion (cells ·) tiling.disjoint
  simp_rw [tiling.union, card_board, card_domino, sum_const] at this
  rw [this]
  ring

-- Classification of dominos

def horizontal : Domino → Prop
| Domino.H _ => True
| Domino.V _ => False

def vertical : Domino → Prop
| Domino.H _ => False
| Domino.V _ => True

lemma disjoint_hv : Disjoint (horizontal · : Domino → Prop) (vertical ·) := by
  apply Pi.disjoint_iff.mpr
  intros
  unfold horizontal vertical
  split <;> simp

lemma either_hv : ∀ x, horizontal x ∨ vertical x := by
  intros
  unfold horizontal vertical
  split <;> simp

-- Decomposition of tiling into horizontal and vertical parts

def htiles (tiling : DominoTiling n m) : Finset Domino :=
  tiling.tiles.filter (horizontal ·)

def vtiles (tiling : DominoTiling n m) : Finset Domino :=
  tiling.tiles.filter (vertical ·)

lemma disjoint_hvtiles (tiling : DominoTiling n m) :
  Disjoint (htiles tiling) (vtiles tiling) := by
  unfold htiles vtiles
  apply disjoint_filter_filter'
  exact disjoint_hv

lemma union_hvtiles (tiling : DominoTiling n m) :
  disjUnion (htiles tiling) (vtiles tiling) (disjoint_hvtiles tiling) = tiling.tiles := by
  rw [disjUnion_eq_union]
  ext x
  constructor
  case mp =>
    intro hx
    cases mem_union.mp hx
    case inl hx =>
      unfold htiles at hx
      exact mem_of_mem_filter x hx
    case inr hx =>
      unfold vtiles at hx
      exact mem_of_mem_filter x hx
  case mpr =>
    intro hx
    rw [mem_union]
    cases x
    case H lft =>
      left
      unfold htiles
      apply mem_filter.mpr
      simp [hx, horizontal]
    case V top =>
      right
      unfold vtiles
      apply mem_filter.mpr
      simp [hx, vertical]

lemma card_hvtiles (tiling : DominoTiling n m) :
  #(htiles tiling) + #(vtiles tiling) = #tiling.tiles := by
  rw [←card_disjUnion (h := disjoint_hvtiles tiling), union_hvtiles]

-- Lemmas for the main theorem

lemma x_sum_board :
  ∑ pt ∈ board n m, pt.x = n*(n-1)/2 * m := by
  calc
    ∑ pt ∈ board n m, pt.x =
      ∑ pt ∈ range n ×ˢ range m, pt.1 := by
      apply sum_map
    _ = ∑ x ∈ range n, ∑ y ∈ range m, x := by
      apply sum_product
    _ = ∑ y ∈ range m, ∑ x ∈ range n, x := by
      apply sum_comm
    _ = ∑ y ∈ range m, n*(n-1)/2 := by
      rw [sum_range_id]
    _ = #(range m) * (n*(n-1)/2) := by
      simp [sum_const_nat]
    _ = (n*(n-1)/2) * m := by
      rw [card_range, mul_comm]

lemma x_parity_tiling (tiling : DominoTiling n m) :
  n*(n-1)/2*m ≡ #(htiles tiling) [MOD 2] := by
  calc
    n*(n-1)/2*m % 2 = (∑ pt ∈ board n m, pt.x % 2) % 2 := by
      rw [←x_sum_board, sum_nat_mod]
    _ = (∑ tile ∈ tiling.tiles, ∑ pt ∈ cells tile, pt.x % 2) % 2 := by
      rw [←tiling.union, sum_disjiUnion]
    _ = (∑ tile ∈ tiling.tiles, (∑ pt ∈ cells tile, pt.x % 2) % 2) % 2 := by
      rw [sum_nat_mod]
    _ = (∑ tile ∈ tiling.tiles, (∑ pt ∈ cells tile, pt.x) % 2) % 2 := by
      congr! 2
      rw [←sum_nat_mod]
    _ = ((∑ tile ∈ htiles tiling, (∑ pt ∈ cells tile, pt.x) % 2) +
      (∑ tile ∈ vtiles tiling, (∑ pt ∈ cells tile, pt.x) % 2)) % 2 := by
      rw [←union_hvtiles tiling, sum_disjUnion (disjoint_hvtiles tiling)]
    _ = ((∑ tile ∈ htiles tiling, 1) + (∑ tile ∈ vtiles tiling, 0)) % 2 := by
      congr! with tile tile_mem_htiles tile tile_mem_vtiles
      · cases htile : tile with
        | H lft => simp [cells]; omega
        | V top => simp [htiles, htile, horizontal] at tile_mem_htiles
      · cases htile : tile with
        | H lft => simp [vtiles, htile, vertical] at tile_mem_vtiles
        | V top => simp [cells]; omega
    _ = (∑ i ∈ htiles tiling, 1) % 2 := by
      rw [sum_const_zero, add_zero]
    _ = #(htiles tiling) % 2 := by
      simp [sum_const_nat]

-- Main theorem

theorem puzzle (tiling : DominoTiling 10 10) :
  #(htiles tiling) ≠ #(vtiles tiling) := by
  by_contra
  have card_htiles : #(htiles tiling) = 25 := by
    have := card_hvtiles tiling
    have := card_tiling tiling
    omega
  have := x_parity_tiling tiling
  simp [card_htiles, Nat.ModEq] at this
