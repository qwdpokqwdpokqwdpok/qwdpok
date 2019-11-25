(*

~~~~~~~~~~~luzne przemyslenia~~~~~~~~~~~

jezeli t ma wysokosc h to ma
co najmniej (2 ^ ( (h - 2) +1 ) - 1) + ((2 ^ (h - 1)) / 2 + 1) + 1 elementow = 2 ^ (h - 1) + 2 ^ (h - 2) + 1
i co najwyzej 2 ^ (h + 1) - 1 elementow
stosunek elementow po jednej stronie korzenia do elementow po drugiej stronie korzenia jest lepszy niz 3 : 8 przy tej samej wysokosci poddrzew

do remove (x, y) potrzebne sa przedzialy mniejsze od x i wieksze od y, mozna uzyc funkcji split na x i na y
do add (x, y) tez potrzbene przedzialy mniejsze od x i wieksze od y

do below potrzebna jest ilosc liczb, mozna od razu przechowywac te informacje obok wysokosci

*)













(*===========*)
(* poddrzewo, przedzial, poddrzewo, wysokosc, ilosc liczb *)
type t =
  | Empty
  | Node of t * (int * int) * t * (int * int)

let empty =
    Empty

let is_empty set = 
  set = Empty

(* dodawanie z uwzglednieniem max_int i min_int *)
let safe_add x y =
    if x >= 0 && y >= 0 && x >= max_int - y then max_int
    else if x <= 0 && y <= 0 && x <= min_int - y then min_int
    else x + y

let height = function
  | Node (_, _, _, (h, _)) -> h
  | Empty -> 0

let number_of_elements = function
  | Node (_, _, _, (_, n)) -> n
  | Empty -> 0

let make l ((x, y) as k) r =
    Node (l, k, r, (max (height l) (height r) + 1,
        (safe_add (safe_add (number_of_elements l) (number_of_elements r)) (y - x + 1))))

(* compare dla przedzialow *)
let cmp (a, b) (c, d) =
    if b < c then -1
    else if d < a then 1
    else 0

(* bal z pSet ze zmianami ze wzgledu na typ t (* zmiana tylko w ostatniej linijce *) *)
(* wlasciwie czemu +2, a nie +1 ??????????? *)
let bal l k r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _) ->
        if height ll >= height lr then make ll lk (make lr k r)
        else
          (match lr with
          | Node (lrl, lrk, lrr, _) ->
              make (make ll lk lrl) lrk (make lrr k r)
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _) ->
        if height rr >= height rl then make (make l k rl) rk rr
        else
          (match rl with
          | Node (rll, rlk, rlr, _) ->
              make (make l k rll) rlk (make rlr rk rr)
          | Empty -> assert false)
    | Empty -> assert false
  else make l k r

(* jezeli przedzial nie przecina zadnego sposrod przedzialow do ktorych go dodajemy,
mozna uzyc add_one z pSet z malymi zmianami

funkcja znajduje miejsce, w ktorym mozna umiescic przedzial,
a nastepnie wykonuje bal co najwyzej tyle razy, ile wynosi wysokosc wynikowego drzewa *)
let rec add_separate ((a, b) as x) = function
  | Node (l, k, r, h) ->
      let c = cmp x k in
      if c = 0 then Node (l, x, r, h)
(* oczywiscie c <> 0, bo przedzialy sa rozlaczne *)
      else if c < 0 then
        let nl = add_separate x l in
        bal nl k r
      else
        let nr = add_separate x r in
        bal l k nr
  | Empty -> Node (Empty, x, Empty, (1, (b - a + 1)))
(* mozna dac dowolna liczbe jako wysokosc "Empty" *)

(* analogicznie z funkcja join (* zmiana tylko przy (lh, _) i (rh, _) i nazwach funkcji *)
z kazdym krokiem rekurencyjnym zmniejsza sie wysokosc wynikowynikowego drzewa
bal wykonuje sie raz w kazdym kroku *)
let rec join_separate l v r =
  match (l, r) with
    (Empty, _) -> add_separate v r
  | (_, Empty) -> add_separate v l
  | Node (ll, lv, lr, (lh, _)), Node(rl, rv, rr, (rh, _)) ->
      if lh > rh + 2 then bal ll lv (join_separate lr v r) else
      if rh > lh + 2 then bal (join_separate l v rl) rv rr else
      make l v r

let split x set =
  let rec loop x = function
      Empty ->
        (Empty, false, Empty)
    | Node (l, ((a, b) as v), r, _) ->
        let c = cmp (x, x) v in
(* jezeli x jest w (a, b) *)
        if c = 0 then
(* lewa strona *)
            ((if x = a then l else add_separate (a, x - 1) l),
            true,
(* prawa strona *)
            (if x = b then r else add_separate (x + 1, b) r))
(* jezeli x nie jest w (a, b) *)
        else if c < 0 then
          let (ll, pres, rl) = loop x l in (ll, pres, join_separate rl v r)
        else
          let (lr, pres, rr) = loop x r in (join_separate l v lr, pres, rr)
  in loop x set

(* bez zmian *)
let rec min_elt = function
  | Node (Empty, k, _, _) -> k
  | Node (l, _, _, _) -> min_elt l
  | Empty -> raise Not_found

(* bez zmian *)
let rec remove_min_elt = function
  | Node (Empty, _, r, _) -> r
  | Node (l, k, r, _) -> bal (remove_min_elt l) k r
  | Empty -> invalid_arg "PSet.remove_min_elt"

(* bez zmian *)
(* t1 musi miec wszystkie elementy mniejsze o co najmniej 2 od najmniejszego elementu t2 *)
let merge t1 t2 =
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ ->
      let k = min_elt t2 in
      bal t1 k (remove_min_elt t2)

(* split x set to przedzialy mniejsze od x (polaczone w drzewo t),
split y set to przedzialy wieksze od y,
wyniki spelniaja specyfikacje merge *)
let remove (x, y) set =
    let (t1, _, _) = split x set in
    let (_, _, t2) = split y set
    in merge t1 t2

(* do add x set potrzebne sa przedzialy set, ktore przecinaja x lub sa oddalone od x o 1
nastepnie set bez tych przedzialow i x mozna polaczyc funkcja join_separate *)

(* compare dla przedzialow, ale przedzialy musza byc oddalone o co najmniej 2 *)
let cmp1 (a, b) (c, d) =
    if safe_add b 1 < c then -1
    else if safe_add d 1 < a then 1
    else 0

let rec cross ((a, b) as x) = function
    | Node (l, ((ka, kb) as k), r, _) ->
        if cmp1 x k = 0 then
            let (lcross, _) = cross x l in
            let (_, rcross) = cross x r
            in min lcross (min a ka), max rcross (max b kb)
        else if cmp1 x k < 1 then
            cross x l
        else cross x r
    | Empty -> x

let add x set =
    let ((xa, xb) as xx) = cross x set in
    let (l, _, _) = split xa set in
    let (_, _, r) = split xb set in
    join_separate l xx r

(* bez zmian *)
let mem x set =
  let rec loop = function
    | Node (l, k, r, _) ->
        let c = cmp x k in
        c = 0 || loop (if c < 0 then l else r)
    | Empty -> false in
  loop set

(* bez zmian *)
let iter f set =
  let rec loop = function
    | Empty -> ()
    | Node (l, k, r, _) -> loop l; f k; loop r in
  loop set

(* bez zmian *)
let fold f set acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, k, r, _) ->
          loop (f k (loop acc l)) r in
  loop acc set

(* bez zmian *)
let elements set = 
  let rec loop acc = function
      Empty -> acc
    | Node(l, k, r, _) -> loop (k :: loop acc r) l in
  loop [] set

let below x set =
    let (l, present, r) = split x set in
    safe_add (number_of_elements l) (if present then 1 else 0)























