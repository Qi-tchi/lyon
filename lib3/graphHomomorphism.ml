module MGraph = MGraph
module Arrow = MGraph.Arrow
module Node = MGraph.Node
module NodeMap = Map.Make(Node)
module ArrowMap = MGraph.ArrowMap
module ArrowSet = MGraph.ArrowSet
module NodeSet = MGraph.NodeSet
module LabelSet = MGraph.LabelSet
(*  def graph homomorphism *) 

module GraphHomo = struct 
  type t = {
    dom : MGraph.Graph.t;
    codom : MGraph.Graph.t;
    hv : Node.t NodeMap.t;
    he : Arrow.t ArrowMap.t;
  }
  (* alphb order *)
  let compare h h' = 
    let r = MGraph.compare h.dom h'.dom in
    if r <> 0 then r else
    let r = MGraph.compare h.codom h'.codom in
    if r <> 0 then r else
    let r = NodeMap.compare Node.compare h.hv h'.hv in
    if r <> 0 then r else
    ArrowMap.compare Arrow.compare h.he h'.he
  let equal f g = compare f g = 0
end
include GraphHomo
module GraphHomoSet = Set.Make(GraphHomo)
module GraphHomoMap = Map.Make(GraphHomo)
let hv h = h.hv
let he h = h.he
let dom h = h.dom
let codom h = h.codom
let labels {dom;codom;hv=_;he=_;} = 
  let labelsD, labelsC = MGraph.labels dom, MGraph.labels codom in
   LabelSet.union labelsD labelsC
let hvFromList l = List.map (fun (s,t) -> (Node.fromInt s, Node.fromInt t)) l |> List.to_seq |> NodeMap.of_seq
let heFromList l = List.map (fun (s,t) -> (Arrow.fromInt s, Arrow.fromInt t)) l |> List.to_seq |> ArrowMap.of_seq
let hvX hv x = assert(NodeMap.mem x hv) ; NodeMap.find x hv
let heX he x = assert(ArrowMap.mem x he) ; ArrowMap.find x he
(** value of [x] by [he] *)
let fromGraphsAndMaps g g' hv he  =
  let dom_hv, img_hv =
    NodeMap.bindings hv |> List.map fst |> NodeSet.of_list, 
    NodeMap.bindings hv |> List.map snd |> NodeSet.of_list in
  let dom_he, img_he =
    ArrowMap.bindings he |> List.map fst |> ArrowSet.of_list, 
    ArrowMap.bindings he |> List.map snd |> ArrowSet.of_list in
  (* hv well defined function from V(g) to V(g') *)
  assert(NodeSet.equal dom_hv (MGraph.nodes g)); 
  assert(NodeSet.subset img_hv (MGraph.nodes g'));
  (* he well defined function from E(g) to E(g') *)
  assert(ArrowSet.equal dom_he (MGraph.arrows g));
  assert(ArrowSet.subset img_he (MGraph.arrows g'));
  (* arrows are preserved *)
  assert (
    let ars = MGraph.arrows g in
    ArrowSet.for_all 
    (fun x -> let y = heX he x in 
              (*  he(sx, label, tx) = (hv(sx),label, hv(tx)) *)
              let xs,xt = MGraph.srcDstOf g x in
              let xs',xt' = hvX hv xs, hvX hv xt in
              let ys,yt = MGraph.srcDstOf g' y in
              Node.equal xs' ys && Node.equal xt' yt &&
              MGraph.labelOf g x |> MGraph.Label.equal (MGraph.labelOf g' y)
              )
    ars);
  {dom = g; codom = g'; hv=hv;he=he}
let fromGraphsAndMaps_opt g g' hv he =
  try Some (fromGraphsAndMaps g g' hv he) with _ -> None
let hvToStr ?(sep=";") hv = 
  hv |> NodeMap.bindings |> List.map (fun (x,y) -> Printf.sprintf "(%s,%s)" (Node.toStr x) (Node.toStr y)) |> String.concat sep |> Printf.sprintf "[%s]"
let heToStr ?(sep=";") he  = 
  (* he |> ArrowMap.bindings |> List.map (fun (x,y) -> Printf.sprintf "(%s,%s)" (Arrow.toStr x) (Arrow.toStr y)) |> String.concat sep |> Printf.sprintf "[%s]" *)
    let bingdings = he |> ArrowMap.bindings in
    let ss = bingdings |> List.map 
      (fun (x,y) -> 
        let xs = (Arrow.toStr x) in 
        let ys = (Arrow.toStr y) in 
        Printf.sprintf "%s %s" xs ys) in (* to do : why we can not use (%s,%s) *)
    let s = String.concat sep ss in
     Printf.sprintf "[%s]" s
    
let fromGraphsAndMaps_exn g g' hv he =
  try fromGraphsAndMaps g g' hv he with _ -> 
  raise (Failure
    (Printf.sprintf 
      "g:
      %sg':
      %shv:
      %she:%s"
    (g|> MGraph.toStr) (g' |> MGraph.toStr)
    (hvToStr hv) (heToStr he)))

(* 
g:\n      
nodes : [ 1;2 ]\n
arrows : [ (1,0,2,2);(1,a,1,1);(2,X,2,3) ]
g':\n      
nodes : [ 0;1 ]
\narrows : [ (0,0,1,6);(0,1,1,7);(0,A,1,8);(0,X,1,9);
             (0,a,1,10);(0,0,0,1);(0,1,0,2);(0,A,0,3);
             (0,X,0,4);(0,a,0,5);(1,0,1,16);(1,1,1,17);
             (1,A,1,18);(1,X,1,19);(1,a,1,20);(1,0,0,11);
             (1,1,0,12);(1,A,0,13);(1,X,0,14);(1,a,0,15) ]
hv:\n      [(1,1);(2,0)]
he:[(1,10);(2,11);(3,4)]
*)

let imgOf h = 
  let codom, hv, he = codom h, hv h, he h in 
  let img_hv = hv |> NodeMap.bindings |> List.map snd |> NodeSet.of_list in
  let img_he = he |> ArrowMap.bindings |> List.map snd |> ArrowSet.of_list in
  MGraph.subgraphFrom codom img_hv img_he

  
  
  (* let imgOfKByH (k : 'b  graph) (h : 'b homomorphism) =
    assert (isIncludedAsSet k.vertices h.dom.vertices ~compare:compareVertex);
    assert (isIncludedAsSet k.edges h.dom.edges ~compare:compareEdge);
    let vs = imgOf h.hv k.vertices ~compareDom:compareVertex ~compareCod:compareEdge in
    let es = imgOf h.he k.edges ~compareDom:compareEdge ~compareCod:compareEdge in
    mgraphFromVerticesAndEdges vs es *)
  
  

(* let fromGraphsAndMaps_try dom codom hv he = try Some( fromGraphsAndMaps dom codom hv he) with _ -> None  *)
(* constructor with lists *)
let fromList domVList domEList codomVList codomEList hv he =
  let dom = MGraph.fromList domVList domEList in
  let codom = MGraph.fromList codomVList codomEList in
  let hv = List.map (fun (x,y) -> (x |> Node.fromInt, y |> Node.fromInt)) hv |> List.to_seq |> NodeMap.of_seq in
  let he = List.map (fun (x,y) -> (x |> Arrow.fromInt, y |> Arrow.fromInt)) he 
   |> List.to_seq |> ArrowMap.of_seq in
  fromGraphsAndMaps dom codom hv he
 
(* begin test *)
let%expect_test _ = 
  let h = fromList 
    (* 1-a:1->2  3-a:2->4 *)
    [1;2;3;4] [(1,"a",2,1);(3,"a",4,2)]
    (* 1-a:1->3  3-b:2->4 -a:3-> 2 *)
     [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3)]
    [(1,1);(2,3);(3,1);(4,3)] [(1,1); (2,1)] in
  print_string (imgOf h |> MGraph.toStr)
  ;[%expect {|
  nodes : [ 1;3 ]
  arrows : [ (1,a,3,1) ]
  |}]

(* begin test *)
(* test not structure preserving *)
let%test _ = 
  try
    fromList 
      (*    1 -a:1-> 1   2   3  *)
      [1;2;3] [(1,"a",1,1)] 
      (*    1 -a:1-> 3 -b:2-> 4 -a:3-> 2    *)
      [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3);]
      [(1,1);(2,3);(3,4)] 
      [(1,1)] |> ignore ; false
  with _ -> true

(* test not structure preserving *)
let%test _ = 
  try 
    fromList 
    (*    1 -a:1-> 2     *)
    [1;2] [(1,"a",2,1)]
    (*    1 -a:1-> 3 -b:2-> 4 -a:3-> 2    *)
    [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3)]
    [(1,1);(2,2)]
    [(1,3)] |> ignore; false
  with _ -> true

(* test codom not eq [codom h] *)
  let%expect_test "" = 
    (*    1 -a:1-> 2     *)
    let g = MGraph.fromList [1;2] [(1,"a",2,1)] in
    (*    1 -a:1-> 3 -b:2-> 4 -a:3-> 2    *)
    let g' = MGraph.fromList [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3)] in
    let hv = hvFromList [(1,4);(2,2)] in
    let he = heFromList [(1,3)] in
    let sg,tg = MGraph.srcDstOf g 1 in
    let sg',tg' = MGraph.srcDstOf g' 3 in
    Printf.printf "img of (%d,%s,%d,%d) is (%d,%s,%d,%d)" sg (MGraph.labelOf g 1) tg 1 sg' (MGraph.labelOf g' 3) tg' 1; 
    (g,g',hv,he) |> ignore;
    fromGraphsAndMaps g g' hv he |> ignore;
    [%expect{|
    img of (1,a,2,1) is (4,a,2,1)
    |}]
(* test not defined on node 2  *)
let%test _ = 
  try 
    fromList 
    (*    1 -a:1-> 2     *)
    [1;2] [(1,"a",2,1)]   
    (*    1 -a:1-> 3 -b:2-> 4 -a:3-> 2    *)
    [1;2;3;4]  [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3)]
    [(1,2)] [(1,3)] |> ignore; false
  with _ -> true
(* test : well defined *)
let%test _ = 
    fromList 
    [1;2]
    [(1,"a",2,1)]
    [1;2;3;4]
    [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3);]
    [(1,1);(2,3)]
     [(1,1)]   |> ignore; true 
  (* end test *)
let id g =
  assert (MGraph.isGraph g);
  let hv = List.map (fun x -> (x,x)) (MGraph.nodes g |> NodeSet.elements) |>  List.to_seq |>NodeMap.of_seq in
  let he = List.map (fun x -> (x,x)) (MGraph.arrows g |> ArrowSet.elements) |>  List.to_seq |> ArrowMap.of_seq in
  fromGraphsAndMaps g g hv he
  

let isInjOnNodes h = 
  let hv = hv h in 
  let img = 
    hv |> NodeMap.bindings |> List.map snd |> NodeSet.of_list in
  Int.equal (dom h |> MGraph.order) (img |> NodeSet.cardinal)

(* test : injective on vertices*)
let%test _ = 
  fromList [1;2] [(1,"a",2,1)] [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3)] [(1,1);(2,3)] [(1,1)] |> isInjOnNodes
(* test : non injective  vertices*)
let%test _ = 
  fromList [1;2;3] [(1,"a",2,1)] [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3);] [(1,1);(2,3);(3,1)] [(1,1)] |> isInjOnNodes |> not

let isSurjOnNodes h = 
  let hv = hv h in 
  let img = 
    hv |> NodeMap.bindings |> List.map snd |> NodeSet.of_list in
  Int.equal (codom h |> MGraph.order) (img |> NodeSet.cardinal)

let%test _ = 
  fromList [1;2;3;4] [(1,"a",2,1)] [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3)] [(1,1);(2,3);(3,2);(4,4)] [(1,1)] |> isSurjOnNodes
let%test _ = 
  fromList [1;2;3] [(1,"a",2,1)] [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3);] [(1,1);(2,3);(3,1)] [(1,1)] |> isSurjOnNodes |> not
let%test _ = 
  fromList [1;2;3;4] [(1,"a",2,1)] [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3);] [(1,1);(2,3);(3,1);(4,4)] [(1,1)] |> isSurjOnNodes |> not 

let isInjOnArrows h = 
  let he = he h in 
  let 
  (* dom,  *)
  img = 
    (* he |> ArrowMap.bindings |> List.map fst |> ArrowSet.of_list,  *)
    he |> ArrowMap.bindings |> List.map snd |> ArrowSet.of_list in
  Int.equal (dom h |> MGraph.size) (img |> ArrowSet.cardinal)
(* test injective on arrows *)
let%test _ = 
  fromList [1;2;3;4] [(1,"a",2,1);(3,"a",4,2)] [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3)] [(1,1);(2,3);(3,4);(4,2)] [(1,1);(2,3)] |> isInjOnArrows
(* test not injective on edges *)
let%test _ = 
  fromList [1;2;3;4] [(1,"a",2,1);(3,"a",4,2)] [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3)] [(1,1);(2,3);(3,1);(4,3)] [(1,1); (2,1)] |> isInjOnArrows |> not

let isSurjOnArrows h = 
  let he = he h in 
  let img = 
    he |> ArrowMap.bindings |> List.map snd |> ArrowSet.of_list in
  Int.equal (dom h |> MGraph.size) (img |> ArrowSet.cardinal)

(* test injective on arrows *)
let%test _ = 
  fromList [1;2;3;4] [(1,"a",2,1);(3,"a",4,2)] [1;2;3;4] [(1,"a",3,1);(4,"a",2,3)] [(1,1);(2,3);(3,4);(4,2)] [(1,1);(2,3)] |> isSurjOnArrows
(* test not injective on edges *)
let%test _ = 
  fromList [1;2;3;4] [(1,"a",2,1);(3,"a",4,2)] [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3)] [(1,1);(2,3);(3,1);(4,3)] [(1,1); (2,1)] |> isSurjOnArrows |> not
  
let isInj h = 
  (* inj on vertices *)
  isInjOnNodes h &&
  (* inj on edges *)
  isInjOnArrows h
  
let isSurj h = 
  (* inj on vertices *)
  isSurjOnNodes h &&
  (* inj on edges *)
  isSurjOnArrows h
let isIso h = 
  isInj h && isSurj h
  
let isSpan f g = (dom f) |> MGraph.Graph.equal (dom g)
  (* shareDomFonc f.hv g.hv ~compare:compareVertex && shareDomFonc f.he g.he ~compare:compareEdge *)

let isCospan f g = (codom f) |> MGraph.Graph.equal (codom g)
  (* shareCodomFonc f.hv g.hv ~compare:compareVertex && shareCodomFonc f.he g.he ~compare:compareEdge *)
  
let%test "equal" = equal 
  (fromList 
  [1;2;3;4] [(1,"a",2,1);(3,"a",4,2)]  (* g *)
  [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3);] (*h*) 
  [(1,1);(2,3);(3,1);(4,3)]  (*hv*)
  [(1,1);(2,1)])
  (fromList 
  [1;2;3;4] [(1,"a",2,1);(3,"a",4,2)]  (* g *)
  [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3);] (*h*) 
  [(1,1);(2,3);(3,1);(4,3)]  (*hv*)
  [(1,1);(2,1)])

(* test : diff dom *)
let%expect_test "equal" = 
  equal 
  (fromList 
  [1;2;3;4] [(1,"a",2,1);(3,"a",4,2)]  (* g *)
  [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3);] (*h*) 
  [(1,1);(2,3);(3,1);(4,3)]  (*hv*)
  [(1,1);(2,1)])
  (fromList 
  [1;2;3;4] [(1,"a",2,1)]  (* g *)
  [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3);] (*h*) 
  [(1,1);(2,3);(3,1);(4,3)]  (*hv*)
  [(1,1)]) |> Printf.printf "%b"
  ;
  [%expect{|
  false
  |}]


let isComposible f g = MGraph.Graph.equal (codom f) (dom g)

(* begin test *)
let%expect_test "codom" = 
  fromList 
  [1;2]
  []  (* g *)
  [1;2;3;4] [(1,"a",3,1);(4,"a",2,3)] (*h*) 
  [(1,1);(2,2)]  (*hv*)
  [] |> codom |> MGraph.toStr |> print_string
  ;[%expect{|
  nodes : [ 1;2;3;4 ]
  arrows : [ (1,a,3,1);(4,a,2,3) ]
  |}]
let%expect_test "dom" = 
  fromList 
  [1;2;3;4] [(1,"a",3,1);(4,"a",2,3)] (*g*) 
  [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3)] (*h*) 
  [(1,1);(2,2);(3,3);(4,4)]  (*hv*)
  [(1,1); (3,3)] 
  |> dom |> MGraph.toStr |> print_string
  ;[%expect{|
  nodes : [ 1;2;3;4 ]
  arrows : [ (1,a,3,1);(4,a,2,3) ]
  |}]

let%test "isComposible" = isComposible
  (fromList 
  [1;2] []  (* g *)
  [1;2;3;4] [(1,"a",3,1);(4,"a",2,3)] (*h*) 
  [(1,1);(2,2)]  (*hv*)
  [])
  (fromList 
  [1;2;3;4] [(1,"a",3,1);(4,"a",2,3)] (*g*) 
  [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3)] (*h*) 
  [(1,1);(2,2);(3,3);(4,4)]  (*hv*)
  [(1,1); (3,3)])

let rec isComposibleList l = 
    match l with
    | x1::x2::xs -> isComposible x1 x2 && isComposibleList (x2::xs)
    | _ -> true
let composition f g = 
  assert (isComposible f g);
  let dom = dom f in
  let codom = codom g in
  (* hv *)
  let hv_f, hv_g = hv f, hv g in
  let hv = NodeMap.map (fun n -> NodeMap.find n hv_g) hv_f in
  (* he *)
  let he_f, he_g = he f, he g in
  let he = ArrowMap.map (fun n -> ArrowMap.find n he_g) he_f in
  fromGraphsAndMaps dom codom hv he

let rec compositionList xs = 
  assert(List.length xs <> 0);
  assert(isComposibleList xs);
  match xs with
  | y1 :: y2 :: ys -> composition y1 (compositionList (y2::ys))
  | [y] -> y
  | _ -> assert false


let isCommutative xs ys = 
  isComposibleList xs &&
  isComposibleList ys &&
  isSpan (List.hd xs) (List.hd ys) &&
  isCospan (List.hd (List.rev xs)) (List.hd (List.rev ys)) &&
  equal (compositionList xs) (compositionList ys)

(* begin test  *)

let%expect_test "" =
  let f = fromList 
  (*  1  2  *)
  [1;2] []  (* g *)
  (* 1 -a:1-> 3    4 -a:2-> 2 *)
  [1;2;3;4] [(1,"a",3,1);(4,"a",2,2)] (*h*) 
  [(1,1);(2,2)]  (*hv*)
  [] in
  let g = fromList 
  (* 1 -a:1-> 3    4 -a:2-> 2 *)
  [1;2;3;4] [(1,"a",3,1);(4,"a",2,2)] (*g*) 
  (* 1 -a:1-> 3 -b:2-> 4 -a:3-> 2 *)
  [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3)] (*h*) 
  [(1,1);(2,2);(3,3);(4,4)]  (*hv*)
  [(1,1); (2,3)] in
  let h = fromList 
  (*  1  2  *)
  [1;2] [] (*g*) 
  (* 1 -a:1-> 3 -b:2-> 4 -a:3-> 2 *)
  [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3)] (*h*) 
  [(1,1);(2,2)]  (*hv*)
  [] in
  Printf.printf "isComposibleList [f;g] : %b\n" (isComposibleList [f;g]);
  Printf.printf "isComposibleList [h] : %b\n" (isComposibleList [h]);
  (* Printf.printf "isCommutative [f;g] = [h] : %b" (isCommutative [f;g] [h]) *)
  Printf.printf "isSpan (List.hd xs) (List.hd ys) : %b\n" (isSpan (List.hd [f;g]) (List.hd [h]));
  Printf.printf "isCospan (List.hd (List.rev xs)) (List.hd (List.rev ys)) : %b\n" (isCospan (List.hd (List.rev [f;g])) (List.hd (List.rev [h])));
  Printf.printf "comp f g = h : %b\n" (equal (compositionList [f;g]) (compositionList [h]));
  ;[%expect {|
    isComposibleList [f;g] : true
    isComposibleList [h] : true
    isSpan (List.hd xs) (List.hd ys) : true
    isCospan (List.hd (List.rev xs)) (List.hd (List.rev ys)) : true
    comp f g = h : true
    |}]
  (* end test  *)

(* begin test *)
  
  (* test : commutative *)
  let%test "commutative_triangle" = 
    let h_k_rx = fromGraphsAndMaps
      (*  1  2  *)
      (MGraph.fromList [1; 2] []) 
      (* 1 -a:1-> 3    4 -a:3-> 2 *)
      (MGraph.fromList [1; 2; 3; 4] [(1,"a",3,1);(4,"a",2,3)])   (* cod *)
      (hvFromList [(1, 1); (2, 2)])  (*hv*)
      (heFromList []) in
    let h_rx_l = fromGraphsAndMaps
      (* 1 -a:1-> 3    4 -a:3-> 2 *)
      (MGraph.fromList [1; 2; 3; 4] [(1,"a",3,1); (4,"a",2,3)]) (* dom *)
      (* 1 -a:1-> 3 -a:2-> 2 *)
      (MGraph.fromList [1; 2; 3] [(1,"a",3,1); (3,"a",2,2)]) (*cod*)
      (hvFromList [(1, 1); (2, 2); (3, 3); (4, 3)])
      (heFromList [(1,1);(3,2)]) in
    let h_k_l = fromGraphsAndMaps 
      (*  1  2  *)
      (MGraph.fromList [1; 2] [])
      (* 1 -a:1-> 3 -a:2-> 2 *)
      (MGraph.fromList [1; 2; 3] [(1,"a",3,1);(3,"a",2,2)])
      (hvFromList [(1, 1); (2, 2)])
      (heFromList []) in
    isCommutative [h_k_rx; h_rx_l] [h_k_l]
  
  let%test "commutative_triangle" = 
     let f = fromList 
      (*  1  2  *)
      [1;2] []  (* g *)
      (* 1 -a:1-> 3    4 -a:3-> 2 *)
      [1;2;3;4] [(1,"a",3,1);(4,"a",2,3)] (*h*) 
      [(1,1);(2,2)]  (*hv*)
      [] in
    let g = fromList 
      (* 1 -a:1-> 3    4 -a:3-> 2 *)
      [1;2;3;4] [(1,"a",3,1);(4,"a",2,3)] (*g*) 
      (* 1 -a:1-> 3 -b:2-> 4 -a:3-> 2 *)
      [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3)] (*h*) 
      [(1,1);(2,2);(3,3);(4,4)]  (*hv*)
      [(1,1); (3,3)] in
   let h = fromList 
      (*  1  2  *)
      [1;2] [] (*g*) 
      (* 1 -a:1-> 3 -b:2-> 4 -a:3-> 2 *)
      [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3)] (*h*) 
      [(1,1);(2,2)]  (*hv*)
      [] in
    isCommutative [f;g] [h]
  (* end test  *)

let mapsFromTo dom codom =
  (** all possibles maps from [x] to [y] *)
  let rec aux dom img res = 
    if dom <> [] then 
      begin
        let sol = ref [] in
        List.iter 
          (fun e -> 
              List.iter 
              (fun r -> sol := ((List.hd dom,e)::r)::!sol)
              res
          ) 
        img;
        aux (List.tl dom) img !sol
      end
    else res in
  aux dom codom [[]] 

let homSet x y =
  assert (MGraph.isGraph x &&  MGraph.isGraph y);
  let hvs = mapsFromTo (MGraph.nodes x |> NodeSet.elements) (MGraph.nodes y |> NodeSet.elements) in
  let hvs = List.map (fun x -> x |> List.to_seq |> NodeMap.of_seq) hvs in
  let hes = mapsFromTo (MGraph.arrows x |> ArrowSet.elements) (MGraph.arrows y |> ArrowSet.elements) in
  let hes = List.map (fun x -> x |> List.to_seq |> ArrowMap.of_seq) hes  in
  let vsEs = Base.List.cartesian_product hvs hes in
  let homos =  List.filter_map
              (fun (vs,es) -> fromGraphsAndMaps_opt x y vs es) vsEs in 
  homos

(* let%expect_test _ =  
  let l' = MGraph.fromList [1;2] 
      [ (1,"a",2,5);(1,"b",2,6);(1,"a",1,3);(1,"b",1,4);(2,"a",2,9);(2,"b",2,10);(2,"a",1,7);(2,"b",1,8) ] in 
      print_endline (Printf.sprintf "l':\n%s" (l' |> MGraph.toStr));
  let typegraph = MGraph.fromList [0;1]
      [ (0,"a",1,3);(0,"b",1,4);(0,"a",0,1);(0,"b",0,2);(1,"a",1,7);(1,"b",1,8);(1,"a",0,5);(1,"b",0,6) ] in
  print_endline (Printf.sprintf "type graph:\n%s" (typegraph |> MGraph.toStr));
  let tl's = homSet l' typegraph in
  print_endline (Printf.sprintf "|tl's|=%d" (List.length tl's))
  (* List.iteri 
      (fun i tl' ->
        print_endline (Printf.sprintf "tl' %d:\n%s" i (Homo.toStr tl'));
      )
      tl's   *)
  ;[%expect {|
  l':
  nodes : [ 1;2 ]
  arrows : [ (1,a,2,5);(1,b,2,6);(1,a,1,3);(1,b,1,4);(2,a,2,9);(2,b,2,10);(2,a,1,7);(2,b,1,8) ]
  type graph:
  nodes : [ 0;1 ]
  arrows : [ (0,a,1,3);(0,b,1,4);(0,a,0,1);(0,b,0,2);(1,a,1,7);(1,b,1,8);(1,a,0,5);(1,b,0,6) ]
  |}] *)
  
(* let renameDomOfInjHomo f =
  assert(isInj f);
  let newDom = imgOf f in
  let idNewDom = id newDom in
  {idNewDom with codom = (codom f)} *)
(* let existPushoutComplementOfInjHomos f g =
  assert (isInj f && isInj g && isComposible f g);
  (*      A -f-> B -g-> D     *)
  let a = imgOf (composition f g) in
  let b = imgOf g in
  let d = codom g in
  assert(MGraph.isSubGraphOf a b && MGraph.isSubGraphOf b d);
  let cs = MGraph.subGraphs d in
  List.exists (fun c -> MGraph.isSubGraphOf a c &&
                        MGraph.isSubGraphOf c d &&
                        MGraph.equal (MGraph.unionOfSubGraphs b c) d)
              cs *)
let existPushoutComplementOfInjHomos a b d =
  assert(MGraph.isSubGraphOf a b && MGraph.isSubGraphOf b d);
  (* let cs = MGraph.subGraphs d in
  List.exists (fun c -> MGraph.isSubGraphOf a c &&
                        MGraph.isSubGraphOf c d &&
                        MGraph.equal (MGraph.unionOfSubGraphs b c) d)
              cs *)
  let nsa, nsb, nsd = MGraph.nodes a, MGraph.nodes b, MGraph.nodes d in
  let arsa, arsb, arsd = MGraph.arrows a, MGraph.arrows b, MGraph.arrows d in
  let ns = NodeSet.diff nsd nsb |> NodeSet.union nsa in
  let ars = ArrowSet.diff arsd arsb |> ArrowSet.union arsa in
  if MGraph.canFormSubGraph d ns ars then Some (MGraph.subgraphFrom d ns ars) else None

let%expect_test "" = 
  let a = MGraph.fromList [1] [] in
  let a' = MGraph.fromList [3] [] in
  let b = MGraph.fromList [1;3] [(1,"s",3,1)] in
  let d = MGraph.fromList [1;2;3] [(1,"s",3,1); (2,"s",3,2)] in
  begin 
    match existPushoutComplementOfInjHomos a b d with
    |Some x -> x |> MGraph.toStr |> print_string
    |None -> print_string "\na -id-> b -id-> d : no pushout complement\n";
  end;
  begin
    match existPushoutComplementOfInjHomos a' b d with
    |Some x -> print_string "a' -id-> b -id-> d :\n"; x |> MGraph.toStr |> print_string
    |None -> print_string "a -id-> b -id-> d : no pushout complement\n"
  end
  ;
  [%expect {|
    a -id-> b -id-> d : no pushout complement
    a' -id-> b -id-> d :
    nodes : [ 2;3 ]
    arrows : [ (2,s,3,2) ]
    |}]

  (* let g' = renameDomOfInjHomo g in
  let f' = renameDomOfInjHomo (composition f g) in
  if  *)

(* let cardHom x g = hom x g |> List.length
let homInjOnEdges x g = 
  let hs = hom x g in
  List.filter ~f:isInjectiveOnEdgesHomo hs 
  
let cardHomInjOnEdges x g = homInjOnEdges x g |> List.length *)

(* let generate_dot_representation_homo h =
  let node_to_dot (id, l) = Printf.sprintf "id:%d[label=\"id:%s\"]" id l  in
  let edge_to_dot {id=id;s=src; l=label; t=dst} =
    Printf.sprintf "%d -> %d [label=\"%s (id:%d)\"]" src dst label id
  in
  let node_lines = List.map labelledNodes ~f:node_to_dot in
  let edge_lines = List.map edges ~f:edge_to_dot  in
  let dot_lines = "digraph G {\n" :: (node_lines @ edge_lines) @ ["}\n"] in
    String.concat ~sep:"\n" dot_lines *)

let toStr h = 
  let hv_str = hvToStr (h |> hv) in
  let he_str = heToStr (h |> he) in
  Printf.sprintf "dom:\n%s\ncodom:\n%s\nhv:%s\nhe:%s" 
  (dom h |> MGraph.toStr) (codom h |> MGraph.toStr) hv_str he_str
let%expect_test "" = 
  let grs_ex69_variant_r1_r = fromList
  [1;2;3] []
  [1;2;3;4] [(1,"s",3,1); (3,"0",3,2); (2,"s",4,3); (4,"0",4,4)]
  [(1,1);(2,2);(3,3)] 
  [] in 
  toStr grs_ex69_variant_r1_r |> print_string;
  [%expect {|
      dom:
      nodes : [ 1;2;3 ]
      arrows : [  ]
      codom:
      nodes : [ 1;2;3;4 ]
      arrows : [ (1,s,3,1);(2,s,4,3);(3,0,3,2);(4,0,4,4) ]
      hv:[(1,1);(2,2);(3,3)]
      he:[]
  |}] 
  
(* let toStr_hv h sep = 
  h |> hv |> NodeMap.bindings |> List.map (fun (x,y) -> Printf.sprintf "(%s,%s)" (Node.toStr x) (Node.toStr y)) |> String.concat sep
let toStr_he h sep = 
   h |> he |> ArrowMap.bindings |> List.map (fun (x,y) -> Printf.sprintf "(%s,%s)" (Arrow.toStr x) (Arrow.toStr y)) |> String.concat sep *)

(** given a cospan [(f,h)] return [{g | comp g h = f}]  *)
let factorsOfThrought f h = 
  assert(isCospan f h);
  let gs = homSet (dom f) (dom h) in
  List.filter (fun g -> isCommutative [f] [g;h]) gs

let%expect_test "factorsOfThrought" = 
  (*  1 -"a"1-> 3 -"a"2-> 2 *)
  let domh = MGraph.fromList  [1;2;3] [(1,"a",3,1);(3,"a",2,2)]  
  in
  let codomh = MGraph.fromList 
  [ 0;1;2 ]
  [ (0,"a",2,5);(0,"b",2,6);(0,"a",1,3);(0,"b",1,4);(0,"a",0,1);(0,"b",0,2);(1,"a",2,11);(1,"b",2,12);(1,"a",1,9);(1,"b",1,10);(1,"a",0,7);(1,"b",0,8);(2,"a",2,17);(2,"b",2,18);(2,"a",1,15);(2,"b",1,16);(2,"a",0,13);(2,"b",0,14) ] in
  let hv = [(1,0);(3,2);(2,1)] |>  List.to_seq |>NodeMap.of_seq in
  let he = [(1,5);(2,15)] |>  List.to_seq |> ArrowMap.of_seq in
  let h = fromGraphsAndMaps domh codomh hv he in   
  let e = 
    let dome = MGraph.fromList [0;1] [(0,"a",1,1)] in
    let hve =   [(0,0);(1,2)] |> List.to_seq |>NodeMap.of_seq  in
    let hee =  [(1,5)] |> List.to_seq |> ArrowMap.of_seq  in 
    fromGraphsAndMaps dome codomh hve hee in  
  let gs =factorsOfThrought e h in 
  print_endline ("|{ - star h = e }| = " ^ string_of_int (gs |> List.length))
  ;[%expect {|
  |{ - star h = e }| = 1
  |}];;