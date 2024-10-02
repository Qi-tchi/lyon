module Homo = GraphHomomorphism
module Grs = GraphRewritingSystem
module RuleSet = GraphRewritingSystem.RuleSet

module MGraph = struct 
  include MGraph
  let iso g g' = 
    let homos = Homo.homSet g g' in
    List.exists Homo.isIso homos
end


(* let calculateAllOccurrenceOfXInG g x =
  let occurrences = List.map ~f:imgOfHomomorphism (hom x g) in 
  occurrences *)

(* let calculateRx rl (x : 'b mgraph) :'b mgraph = 
  (* let vertices_powerset = powerset x.vertices in
  let edges_powerset = powerset x.edges in
  (* generate all structures formed by a subset of nodes and a subset of edges X *)
  let structures = List.cartesian_product vertices_powerset edges_powerset in
    (* List.fold_left (fun acc vertices -> List.fold_left (fun acc' edges -> (vertices, edges)::acc') acc edges_powerset ) [] vertices_powerset in *)
  (* filter : structures should be propre connected sub-graphs of X *)
  let propreConnectedSubGraphs = List.filter_map
    ~f:(fun (vs,es) -> 
      try let s = mgraphFromVerticesAndEdges vs es in
          if is_proper_subgraph s x && isConnectedMGraph s then Some s else None
       with _ -> None)
    structures in *)

  (* all subgraphs *)
  let subgraphs = subGraphsOf x in
  (* propre *)
  let propreSubgraphs = List.filter ~f:(is_proper_subgraph ~hostGraph:x) subgraphs in
  (* connected *)
  let propreConnectedSubGraphs = List.filter ~f:isConnectedMGraph propreSubgraphs in
  (* generate all occurrences of these sub-graphs in R *) 
  let occurrences = List.map ~f:(calculateAllOccurrenceOfXInG rl.r.codom) propreConnectedSubGraphs |> List.concat in
  (* filter : occurrences inter Im(r) should not be empty *)
  let occurrencesIntersectImgOfKInR = 
    let imr = imgOfHomomorphism rl.r in
    List.filter ~f:(fun o -> List.exists ~f:(fun v -> isVertex imr v) o.vertices ) occurrences in
  (* take union of all occs *)
  let rx = List.fold_left ~f:(fun acc o -> subgraphUnion acc o) ~init:(mgraphFromLists [] []) occurrencesIntersectImgOfKInR in 
  (* containing K *)
  let rx = subgraphUnion rx (imgOfHomomorphism rl.r) in
  rx *)

(************************
    calculateRx et ses aux funcs
****************************)
let calculateRx rl x = 
  assert(x |> MGraph.isConnected); 
  let r = Grs.rhs rl in
  let rightGraph = Grs.rightGraph rl in
  let interfaceGraph = Grs.interfaceGraph rl in
  (* calculate all possible (r',k') *)
  let r's = MGraph.propreSubgraphs x in
  (* let r's = List.filter (fun sg -> MGraph.isSingleton sg |> not) r's in *)
  let k'r's = List.map 
    (fun r' -> let k's = MGraph.subGraphs r' in
               Base.List.cartesian_product [r'] k's)
     r's 
    |> List.concat in
  (* filter : pushout complement with inj homos exsit *)
  let k'r's = List.filter
    (fun (r',k') -> match Homo.existPushoutComplementOfInjHomos k' r' x with  
                  |Some _ -> true |None -> false) 
    k'r's in
  (* all possible (h_k'r', h_r'r, hk'k) *)
  let triples = 
    List.map 
    (fun (r',k') ->
      let h_k'r' = {(Homo.id k') with codom = r'} in
      let hr'rs = Homo.homSet r' rightGraph in
      let hk'ks = Homo.homSet k' interfaceGraph in
      Base.List.cartesian_product [h_k'r'] (Base.List.cartesian_product hr'rs hk'ks))
    k'r's 
    |> List.concat in
  (* filter : isCommutative *)
  let triples = 
    List.filter 
    (fun (hk'r', (hr'r, hk'k)) -> 
      Homo.isCommutative [hk'r'; hr'r] [hk'k; r])
      triples in
  (* Rx as the union of img of h_r'r *)
  let square = 
    List.map 
    (fun (_, (hr'r, _)) -> Homo.imgOf hr'r)
    triples in
  (* Im(r) is subgraph of Rx *)
  let rx_init = Homo.imgOf r in
  (* all Im(h_r'r) calculated is subgraph of Rx *)
  List.fold_left (fun acc g -> MGraph.unionOfSubGraphs acc g) rx_init square

let%expect_test "calculateRx" = 
  let bruggink_2014_example_4_l = Homo.fromList
    [1;2] [] 
    [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
    [(1,1);(2,2)] [] in
  let bruggink_2014_example_4_r = Homo.fromList 
    [1;2] []
    [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3);]
    [(1,1);(2,2)] [] in
  let bruggink_2014_example_4 = Grs.fromHomos bruggink_2014_example_4_l     bruggink_2014_example_4_r in
  let x = MGraph.fromList [1;3;4] [(1,"a",3,1);(3,"a",4,2)] in
  calculateRx bruggink_2014_example_4 x |> MGraph.toStr |> print_string
  ;
  [%expect{|
      nodes : [ 1;2;3;4 ]
      arrows : [ (1,a,3,1);(4,a,2,3) ]
  |}]
let%expect_test "calculateRx" = 
  let grs_ex69_r1_r = Homo.fromList 
    [1;2;3] [(1,"s",3,1);(3,"0",3,2)]
    [1;2;3;4] [(1,"s",3,1);(3,"0",3,2); (2,"s",4,3); (4,"0",4,4)]
    [(1,1);(2,2);(3,3)] 
    [(1,1); (2,2)] in 
  let grs_ex69_r1_l = Homo.fromList 
    [1;2;3] [(1,"s",3,1);(3,"0",3,2)]
    [1;2;3] [(1,"s",3,1);(3,"0",3,2); (2,"s",3,3)]
    [(1,1);(2,2);(3,3)] 
    [(1,1); (2,2)] in
  let grs_ex69_r1 = Grs.fromHomos grs_ex69_r1_l grs_ex69_r1_r in
  let x = MGraph.fromList [1;2;3] [(1,"s",3,1);(2,"s",3,2)] in
  let x' = MGraph.fromList [1;2;3] [(1,"s",3,1);(2,"s",3,2);(3,"0",3,3)] in
  calculateRx grs_ex69_r1 x |> MGraph.toStr |> Printf.printf "with rx : 1 -s:1-> 3 <-s:2-2\n%s\n";
  calculateRx grs_ex69_r1 x' |> MGraph.toStr |> Printf.printf "with rx :     1 -s:1-> 3 <-s:2-2   3 ->0:3->3\n%s\n"
  ;(*  rx :     1 -s:1-> 3 <-s:2-2   *) 
  [%expect{|
    with rx : 1 -s:1-> 3 <-s:2-2
    nodes : [ 1;2;3 ]
    arrows : [ (1,s,3,1);(3,0,3,2) ]
    with rx :     1 -s:1-> 3 <-s:2-2   3 ->0:3->3
    nodes : [ 1;2;3 ]
    arrows : [ (1,s,3,1);(3,0,3,2) ]
  |}]
let%expect_test "calculateRx" = 
  let grs_ex69_variant_r1_r = Homo.fromList 
    [1;2;3] []
    [1;2;3;4] [(1,"s",3,1);(3,"0",3,2); (2,"s",4,3); (4,"0",4,4)]
    [(1,1);(2,2);(3,3)] 
    [] in 
  let grs_ex69_variant_r1_l = Homo.fromList 
    [1;2;3] []
    [1;2;3] [(1,"s",3,1);(3,"0",3,2); (2,"s",3,3)]
    [(1,1);(2,2);(3,3)] 
    [] in
  let grs_ex69_variant_r1 = Grs.fromHomos grs_ex69_variant_r1_l grs_ex69_variant_r1_r in
  let x = MGraph.fromList [1;2;3] [(1,"s",3,1);(2,"s",3,2)] in
  let x' = MGraph.fromList [1;2;3] [(1,"s",3,1);(2,"s",3,2);(3,"0",3,3)] in
  calculateRx grs_ex69_variant_r1 x |> MGraph.toStr |> Printf.printf "with rx : 1 -s:1-> 3 <-s:2-2\n%s\n";
  calculateRx grs_ex69_variant_r1 x' |> MGraph.toStr |> Printf.printf "with rx :     1 -s:1-> 3 <-s:2-2   3 ->0:3->3\n%s\n"
  ;(*  rx :     1 -s:1-> 3 <-s:2-2   *) 
  [%expect{|
    with rx : 1 -s:1-> 3 <-s:2-2
    nodes : [ 1;2;3 ]
    arrows : [ (1,s,3,1) ]
    with rx :     1 -s:1-> 3 <-s:2-2   3 ->0:3->3
    nodes : [ 1;2;3 ]
    arrows : [ (1,s,3,1);(3,0,3,2) ]
  |}]
let calculateHomomorphismFromRxToR r rx =  
  assert(MGraph.isSubGraphOf rx r);
  {(Homo.id rx) with codom = r}

let calculateHomomorphismFromKToRx k rx =  
  assert(MGraph.isSubGraphOf k rx);
  {(Homo.id k) with codom = rx}

let calculateHomomorphismFromRxToL rx rl hkrx = 
  let l = Grs.lhs rl in
  let leftGraph = Grs.leftGraph rl in
  (* filter : homomorphism injective on edges from V(Rx) to V(l) *)
  let hs = Homo.homSet rx leftGraph in
  let hsInj = List.filter Homo.isInjOnArrows hs in
  (* filter : commutativity    K -hkrx-> Rx -rxl-> L  ;  K -rl.l->L     *)
  let hsInjCom = List.filter (fun hrxl -> Homo.isCommutative [hkrx; hrxl] [l]) hsInj in
  hsInjCom

let createsMoreXOnTheLeft x rl =
  let rx = calculateRx rl x in
  let h_rx_to_r = calculateHomomorphismFromRxToR rl.r.codom rx in
  let h_k_to_rx = calculateHomomorphismFromKToRx rl.r.dom rx in
  let h_rx_to_ls =  calculateHomomorphismFromRxToL rx rl h_k_to_rx in
  match h_rx_to_ls with 
  | [] -> None
  | h_rx_to_l :: _ -> Some (x, rx, h_k_to_rx, h_rx_to_l, h_rx_to_r)


let createsMoreXOnTheLeftBool graph rule =
  match createsMoreXOnTheLeft graph rule with
  |None -> false
  |Some _ -> true
 

let%expect_test "" = 
  let grs_ex69_variant_r1_r = Homo.fromList 
    [1;2;3] []
    [1;2;3;4] [(1,"s",3,1); (3,"0",3,2); (2,"s",4,3); (4,"0",4,4)]
    [(1,1);(2,2);(3,3)] 
    [] in 
  let grs_ex69_variant_r1_l = Homo.fromList 
    [1;2;3] []
    [1;2;3] [(1,"s",3,1); (3,"0",3,2); (2,"s",3,3)]
    [(1,1); (2,2); (3,3)] 
    [] in
  let grs_ex69_variant_r1 = Grs.fromHomos grs_ex69_variant_r1_l grs_ex69_variant_r1_r in
  let x = MGraph.fromList [1;2;3] [(1,"s",3,1);(2,"s",3,2)] in
  let x' = MGraph.fromList [1;2;3] [(1,"s",3,1);(2,"s",3,2);(3,"0",3,3)] in
  match createsMoreXOnTheLeft x grs_ex69_variant_r1 with
  |None -> Printf.printf "with rx : 1 -s:1-> 3 <-s:2-2 ==> false\n\n";
  |Some (_, rx, h_k_to_rx, h_rx_to_l, h_rx_to_r) -> 
    begin 
      Printf.printf "with rx : 1 -s:1-> 3 <-s:2-2 ==> true\n\n";
      Printf.printf "Rx:\n\n%s\n\nh_k_to_rx:\n\n%s\n\nh_rx_to_l:\n\n%s\n\nh_rx_to_r:\n\n%s\n\n"
        (rx |> MGraph.toStr) (h_k_to_rx |> Homo.toStr) (h_rx_to_l |> Homo.toStr) (h_rx_to_r |> Homo.toStr)
    end;
  match createsMoreXOnTheLeft x' grs_ex69_variant_r1 with
  |None -> Printf.printf "with rx : 1 -s:1-> 3 <-s:2-2   3 ->0:3->3 ==> false\n\n";
  |Some (_, rx, h_k_to_rx, h_rx_to_l, h_rx_to_r) -> 
    begin 
      Printf.printf "with rx : 1 -s:1-> 3 <-s:2-2   3 ->0:3->3 ==> true\n\n";
      Printf.printf "Rx:\n\n%s\n\nh_k_to_rx:\n\n%s\n\nh_rx_to_l:\n\n%s\n\nh_rx_to_r:\n\n%s\n\n"
      (rx |> MGraph.toStr) (h_k_to_rx |> Homo.toStr) (h_rx_to_l |> Homo.toStr) (h_rx_to_r |> Homo.toStr)
    end;
  ; [%expect{|
    with rx : 1 -s:1-> 3 <-s:2-2 ==> true

    Rx:

    nodes : [ 1;2;3 ]
    arrows : [ (1,s,3,1) ]

    h_k_to_rx:

    dom:
    nodes : [ 1;2;3 ]
    arrows : [  ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,s,3,1) ]
    hv:[(1,1);(2,2);(3,3)]
    he:[]

    h_rx_to_l:

    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,s,3,1) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,s,3,1);(2,s,3,3);(3,0,3,2) ]
    hv:[(1,1);(2,2);(3,3)]
    he:[(1,1)]

    h_rx_to_r:

    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,s,3,1) ]
    codom:
    nodes : [ 1;2;3;4 ]
    arrows : [ (1,s,3,1);(2,s,4,3);(3,0,3,2);(4,0,4,4) ]
    hv:[(1,1);(2,2);(3,3)]
    he:[(1,1)]

    with rx : 1 -s:1-> 3 <-s:2-2   3 ->0:3->3 ==> true

    Rx:

    nodes : [ 1;2;3 ]
    arrows : [ (1,s,3,1);(3,0,3,2) ]

    h_k_to_rx:

    dom:
    nodes : [ 1;2;3 ]
    arrows : [  ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,s,3,1);(3,0,3,2) ]
    hv:[(1,1);(2,2);(3,3)]
    he:[]

    h_rx_to_l:

    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,s,3,1);(3,0,3,2) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,s,3,1);(2,s,3,3);(3,0,3,2) ]
    hv:[(1,1);(2,2);(3,3)]
    he:[(1,1);(2,2)]

    h_rx_to_r:

    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,s,3,1);(3,0,3,2) ]
    codom:
    nodes : [ 1;2;3;4 ]
    arrows : [ (1,s,3,1);(2,s,4,3);(3,0,3,2);(4,0,4,4) ]
    hv:[(1,1);(2,2);(3,3)]
    he:[(1,1);(2,2)]
    |}]


let%expect_test "" = 
  let grs_ex69_r1_r = Homo.fromList 
  [1;2;3] [(1,"s",3,1);(3,"0",3,2)]
  [1;2;3;4] [(1,"s",3,1);(3,"0",3,2); (2,"s",4,3); (4,"0",4,4)]
  [(1,1);(2,2);(3,3)] 
  [(1,1); (2,2)] in 
  let grs_ex69_r1_l = Homo.fromList 
  [1;2;3] [(1,"s",3,1);(3,"0",3,2)]
  [1;2;3] [(1,"s",3,1);(3,"0",3,2); (2,"s",3,3)]
  [(1,1);(2,2);(3,3)] 
  [(1,1); (2,2)] in
  let grs_ex69_r1 = Grs.fromHomos grs_ex69_r1_l grs_ex69_r1_r in
  let x = MGraph.fromList [1;2;3] [(1,"s",3,1);(2,"s",3,2)] in
  let x' = MGraph.fromList [1;2;3] [(1,"s",3,1);(2,"s",3,2);(3,"0",3,3)] in
  match createsMoreXOnTheLeft x grs_ex69_r1 with
  |None -> Printf.printf "with rx : 1 -s:1-> 3 <-s:2-2 ==> false\n\n";
  |Some (_, rx, h_k_to_rx, h_rx_to_l, h_rx_to_r) -> 
    begin 
      Printf.printf "with rx : 1 -s:1-> 3 <-s:2-2 ==> true\n\n";
      Printf.printf "Rx:\n\n%s\n\nh_k_to_rx:\n\n%s\n\nh_rx_to_l:\n\n%s\n\nh_rx_to_r:\n\n%s\n\n"
        (rx |> MGraph.toStr) (h_k_to_rx |> Homo.toStr) (h_rx_to_l |> Homo.toStr) (h_rx_to_r |> Homo.toStr)
    end;
  match createsMoreXOnTheLeft x' grs_ex69_r1 with
  |None -> Printf.printf "with rx : 1 -s:1-> 3 <-s:2-2   3 ->0:3->3 ==> false\n\n";
  |Some (_, rx, h_k_to_rx, h_rx_to_l, h_rx_to_r) -> 
    begin 
      Printf.printf "with rx : 1 -s:1-> 3 <-s:2-2   3 ->0:3->3 ==> true\n\n";
      Printf.printf "Rx:\n\n%s\n\nh_k_to_rx:\n\n%s\n\nh_rx_to_l:\n\n%s\n\nh_rx_to_r:\n\n%s\n\n"
      (rx |> MGraph.toStr) (h_k_to_rx |> Homo.toStr) (h_rx_to_l |> Homo.toStr) (h_rx_to_r |> Homo.toStr)
    end;
  ; [%expect{|
  with rx : 1 -s:1-> 3 <-s:2-2 ==> true

  Rx:

  nodes : [ 1;2;3 ]
  arrows : [ (1,s,3,1);(3,0,3,2) ]

  h_k_to_rx:

  dom:
  nodes : [ 1;2;3 ]
  arrows : [ (1,s,3,1);(3,0,3,2) ]
  codom:
  nodes : [ 1;2;3 ]
  arrows : [ (1,s,3,1);(3,0,3,2) ]
  hv:[(1,1);(2,2);(3,3)]
  he:[(1,1);(2,2)]

  h_rx_to_l:

  dom:
  nodes : [ 1;2;3 ]
  arrows : [ (1,s,3,1);(3,0,3,2) ]
  codom:
  nodes : [ 1;2;3 ]
  arrows : [ (1,s,3,1);(2,s,3,3);(3,0,3,2) ]
  hv:[(1,1);(2,2);(3,3)]
  he:[(1,1);(2,2)]

  h_rx_to_r:

  dom:
  nodes : [ 1;2;3 ]
  arrows : [ (1,s,3,1);(3,0,3,2) ]
  codom:
  nodes : [ 1;2;3;4 ]
  arrows : [ (1,s,3,1);(2,s,4,3);(3,0,3,2);(4,0,4,4) ]
  hv:[(1,1);(2,2);(3,3)]
  he:[(1,1);(2,2)]

  with rx : 1 -s:1-> 3 <-s:2-2   3 ->0:3->3 ==> true

  Rx:

  nodes : [ 1;2;3 ]
  arrows : [ (1,s,3,1);(3,0,3,2) ]

  h_k_to_rx:

  dom:
  nodes : [ 1;2;3 ]
  arrows : [ (1,s,3,1);(3,0,3,2) ]
  codom:
  nodes : [ 1;2;3 ]
  arrows : [ (1,s,3,1);(3,0,3,2) ]
  hv:[(1,1);(2,2);(3,3)]
  he:[(1,1);(2,2)]

  h_rx_to_l:

  dom:
  nodes : [ 1;2;3 ]
  arrows : [ (1,s,3,1);(3,0,3,2) ]
  codom:
  nodes : [ 1;2;3 ]
  arrows : [ (1,s,3,1);(2,s,3,3);(3,0,3,2) ]
  hv:[(1,1);(2,2);(3,3)]
  he:[(1,1);(2,2)]

  h_rx_to_r:

  dom:
  nodes : [ 1;2;3 ]
  arrows : [ (1,s,3,1);(3,0,3,2) ]
  codom:
  nodes : [ 1;2;3;4 ]
  arrows : [ (1,s,3,1);(2,s,4,3);(3,0,3,2);(4,0,4,4) ]
  hv:[(1,1);(2,2);(3,3)]
  he:[(1,1);(2,2)]
    |}]


let%expect_test "" = 
  let bruggink_2014_example_4_l = Homo.fromList
  [1;2] [] 
  [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
  [(1,1);(2,2)] [] in
  let bruggink_2014_example_4_r = Homo.fromList 
  [1;2] []
  [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3);]
  [(1,1);(2,2)] [] in
  let bruggink_2014_example_4 = Grs.fromHomos bruggink_2014_example_4_l     bruggink_2014_example_4_r in
  let x = MGraph.fromList [1;2;3] [(1,"a",2,1);(2,"a",3,2)] in
  match createsMoreXOnTheLeft x bruggink_2014_example_4 with
  |None -> Printf.printf "with rx : 1 -a:1-> 2 -a:2-> 3 ==> false\n\n";
  |Some (_, rx, h_k_to_rx, h_rx_to_l, h_rx_to_r) -> 
    begin 
      Printf.printf "with rx : 1 -a:1-> 2 -a:2-> 3 ==> true\n\n";
      Printf.printf "Rx:\n\n%s\n\nh_k_to_rx:\n\n%s\n\nh_rx_to_l:\n\n%s\n\nh_rx_to_r:\n\n%s\n\n"
        (rx |> MGraph.toStr) (h_k_to_rx |> Homo.toStr) (h_rx_to_l |> Homo.toStr) (h_rx_to_r |> Homo.toStr)
    end;
  ;
  [%expect{|
    with rx : 1 -a:1-> 2 -a:2-> 3 ==> true

    Rx:

    nodes : [ 1;2;3;4 ]
    arrows : [ (1,a,3,1);(4,a,2,3) ]

    h_k_to_rx:

    dom:
    nodes : [ 1;2 ]
    arrows : [  ]
    codom:
    nodes : [ 1;2;3;4 ]
    arrows : [ (1,a,3,1);(4,a,2,3) ]
    hv:[(1,1);(2,2)]
    he:[]

    h_rx_to_l:

    dom:
    nodes : [ 1;2;3;4 ]
    arrows : [ (1,a,3,1);(4,a,2,3) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    hv:[(1,1);(2,2);(3,3);(4,3)]
    he:[(1,1);(3,2)]

    h_rx_to_r:

    dom:
    nodes : [ 1;2;3;4 ]
    arrows : [ (1,a,3,1);(4,a,2,3) ]
    codom:
    nodes : [ 1;2;3;4 ]
    arrows : [ (1,a,3,1);(3,b,4,2);(4,a,2,3) ]
    hv:[(1,1);(2,2);(3,3);(4,4)]
    he:[(1,1);(3,3)]
    |}]

let hasMoreOccurrencesOnleft x rl =
  let homoXL = Homo.homSet x (Grs.leftGraph rl) in
  (* let homoXL = List.filter Homo.isInjOnArrows homoXL in *)
  let homoXR = Homo.homSet x (Grs.rightGraph rl) in
  (* let homoXR = List.filter Homo.isInjOnArrows homoXR in *)
  (homoXL |> List.length) >= (homoXR |> List.length)

let%expect_test "hasMoreOccurrencesOnleft" = 
  let grs_ex69_r1_l = Homo.fromList 
  [1;2;3] [(1,"s",3,1);(3,"0",3,2)]
  [1;2;3] [(1,"s",3,1);(3,"0",3,2); (2,"s",3,3)]
  [(1,1);(2,2);(3,3)] 
  [(1,1); (2,2)] in
  let grs_ex69_r1_r = Homo.fromList 
  [1;2;3] [(1,"s",3,1);(3,"0",3,2)]
  [1;2;3;4] [(1,"s",3,1);(3,"0",3,2); (2,"s",4,3); (4,"0",4,4)]
  [(1,1);(2,2);(3,3)] 
  [(1,1); (2,2)] in 
  let grs_ex69_r1 = Grs.fromHomos grs_ex69_r1_l grs_ex69_r1_r in
  let rl = grs_ex69_r1 in
  let x = MGraph.fromList [1;2;3] [(1,"s",3,1);(2,"s",3,3)] in
  let homoXL = Homo.homSet x (Grs.leftGraph rl) in
  let homoXR = Homo.homSet x (Grs.rightGraph rl) in
  Printf.printf "homoXL : %d     homoXR : %d  " (homoXL |> List.length)  (homoXR |> List.length)
  ;[%expect{| homoXL : 4     homoXR : 2 |}]  
let hasStrictlyMoreOccurrencesOnleft x rl =
  let homoXL = Homo.homSet x (Grs.leftGraph rl) in
  (* let homoXL = List.filter Homo.isInjOnArrows homoXL in *)
  let homoXR = Homo.homSet x (Grs.rightGraph rl) in
  (* let homoXR = List.filter Homo.isInjOnArrows homoXR in *)
  (homoXL |> List.length) > (homoXR |> List.length)

type problem = {
  witnesses: (MGraph.Graph.t * Grs.RuleSet.t) list;
  rules : Grs.RuleSet.t;
}
let isEmpty pb = Grs.RuleSet.is_empty pb.rules
let pbFromList rules = {rules = Grs.RuleSet.of_list rules; witnesses =[]}

let isX x ~rules = 
  (* connected *)
  MGraph.isConnected x &&
  (* every rule has more X occurrence on the left *)
  Grs.RuleSet.for_all (hasMoreOccurrencesOnleft x) rules &&
  (* every rule creates more occurrences of X on the left*)
  Grs.RuleSet.for_all (createsMoreXOnTheLeftBool x) rules &&
  (* there is a rule which has strictly more X occurrence on the left *)
  Grs.RuleSet.exists (hasStrictlyMoreOccurrencesOnleft x) rules

let%expect_test "isX" = 
  let grs_ex69_r1_l = Homo.fromList 
  [1;2;3] [(1,"s",3,1);(3,"0",3,2)]
  [1;2;3] [(1,"s",3,1);(3,"0",3,2); (2,"s",3,3)]
  [(1,1);(2,2);(3,3)] 
  [(1,1); (2,2)] in
  let grs_ex69_r1_r = Homo.fromList 
  [1;2;3] [(1,"s",3,1);(3,"0",3,2)]
  [1;2;3;4] [(1,"s",3,1);(3,"0",3,2); (2,"s",4,3); (4,"0",4,4)]
  [(1,1);(2,2);(3,3)] 
  [(1,1); (2,2)] in 
  let grs_ex69_r1 = Grs.fromHomos grs_ex69_r1_l grs_ex69_r1_r in
  let rules = Grs.RuleSet.of_list [grs_ex69_r1] in
  let x = MGraph.fromList [1;2;3] [(1,"s",3,1);(2,"s",3,3)] in
  Printf.printf "isX [x] grs_ex69_r1 = %b" 
      (isX x ~rules)
  ;[%expect{| isX [x] grs_ex69_r1 = true |}]  
  


let rec isTerminating pb =
  match Grs.RuleSet.is_empty pb.rules with
  |true -> pb (* if terminating *)
  |false ->
      begin
        let lhsGraphs = List.map (fun r -> r |> Grs.lhs |> Homo.codom) (pb.rules |> Grs.RuleSet.elements) in
        let subgraphs = List.map MGraph.subGraphs lhsGraphs |> List.concat in
        try let x = List.find (isX ~rules:pb.rules) subgraphs in
            let eliminatedRules, remainedRules = Grs.RuleSet.partition (hasStrictlyMoreOccurrencesOnleft x) pb.rules in 
            isTerminating { witnesses=(x,eliminatedRules)::pb.witnesses; rules= remainedRules}  (* new iteration *)
        with Not_found -> print_endline "termination not proved";pb (* if no rule can be eliminated *)
      end
let interpret pb =
  if pb.rules |> Grs.RuleSet.is_empty then 
    print_endline "Termination proved using ";
    let xs = pb.witnesses |> List.rev in
    List.iteri 
    (fun i (x,_) -> Printf.printf "X%d: \n \ \ \ %s" i (MGraph.toStr x))
    xs
let isTerminatingBool pb = 
  isTerminating pb |> isEmpty
let%expect_test "isTerminating" = 
  let bruggink_2014_example_4_l = Homo.fromList
    [1;2] [] 
    [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
    [(1,1);(2,2)] [] in
  let bruggink_2014_example_4_r = Homo.fromList 
    [1;2] []
    [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3);]
    [(1,1);(2,2)] [] in
  let bruggink_2014_example_4 = Grs.fromHomos bruggink_2014_example_4_l     bruggink_2014_example_4_r in
  let lhsGraphs = List.map (fun r -> r |> Grs.leftGraph) [bruggink_2014_example_4] in
  Printf.printf "\nlhsGraphs: %d" (lhsGraphs |> List.length);
  let subgraphs = List.map MGraph.subGraphs lhsGraphs |> List.concat in
  Printf.printf "\nsubgraphs: %d" (subgraphs |> List.length);
  let x = List.find (isX ~rules:([bruggink_2014_example_4] |> Grs.RuleSet.of_list)) subgraphs in
  Printf.printf "\nfirst x: \n%s" (x |> MGraph.toStr);
  let pb = pbFromList [bruggink_2014_example_4] in
  Printf.printf "\nbruggink_2014_example_4 is terminating : %b" (isTerminatingBool pb);
  let eliminatedRules, remainedRules = Grs.RuleSet.partition (hasStrictlyMoreOccurrencesOnleft x) pb.rules in 
  Printf.printf "\nEliminated: %d rules ;  Remained : %d rules\n"
  (eliminatedRules |> Grs.RuleSet.cardinal) (remainedRules |> Grs.RuleSet.cardinal);
  let pb' = { witnesses=(x,eliminatedRules)::pb.witnesses; rules= remainedRules} in
  Printf.printf "pb' is terminating : %b" (pb' |> isTerminatingBool);
  [%expect{|
    lhsGraphs: 1
    subgraphs: 13
    first x:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    bruggink_2014_example_4 is terminating : true
    Eliminated: 1 rules ;  Remained : 0 rules
    pb' is terminating : true
    |}]

let%expect_test "isTerminating" = 
  let grs_ex69_r1_l = Homo.fromList 
    [1;2;3] [(1,"s",3,1);(3,"0",3,2)]
    [1;2;3] [(1,"s",3,1);(3,"0",3,2); (2,"s",3,3)]
    [(1,1);(2,2);(3,3)] 
    [(1,1); (2,2)] in
  let grs_ex69_r1_r = Homo.fromList 
    [1;2;3] [(1,"s",3,1);(3,"0",3,2)]
    [1;2;3;4] [(1,"s",3,1);(3,"0",3,2); (2,"s",4,3); (4,"0",4,4)]
    [(1,1);(2,2);(3,3)] 
    [(1,1); (2,2)] in 
  let grs_ex69_r1 = Grs.fromHomos grs_ex69_r1_l grs_ex69_r1_r in
  (* let x = MGraph.fromList [1;2;3] [(1,"s",3,1);(2,"s",3,3)] in *)
  let pb = pbFromList [grs_ex69_r1] in
  (* let lhsGraphs = List.map (fun r -> r |> Grs.lhs |> Homo.codom) (pb.rules |> Grs.RuleSet.to_list) in
  let subgraphs = List.map MGraph.subGraphs lhsGraphs |> List.concat in
  Printf.printf "\nisX [x] = %b\n" (isX x ~rules:pb.rules); *)
  (* let pb' =  
    try let x = List.find (isX ~rules:pb.rules) subgraphs in
      let eliminatedRules, remainedRules = Grs.RuleSet.partition (hasStrictlyMoreOccurrencesOnleft x) pb.rules in 
      isTerminating { witnesses=(x,eliminatedRules)::pb.witnesses; rules= remainedRules}  (* new iteration *)
    with Not_found -> pb in *)
  pb |> isTerminatingBool |> Printf.printf "[grs_ex69_r1] is terminating : %b";
  ;[%expect{| [grs_ex69_r1] is terminating : true |}]

let%expect_test "isTerminating" = 
  let grs_ex69_variant_r1_r = Homo.fromList 
  [1;2;3] []
  [1;2;3;4] [(1,"s",3,1); (3,"0",3,2); (2,"s",4,3); (4,"0",4,4)]
  [(1,1);(2,2);(3,3)] 
  [] in 
  let grs_ex69_variant_r1_l = Homo.fromList 
  [1;2;3] []
  [1;2;3] [(1,"s",3,1); (3,"0",3,2); (2,"s",3,3)]
  [(1,1); (2,2); (3,3)] 
  [] in
  let grs_ex69_variant_r1 = Grs.fromHomos grs_ex69_variant_r1_l grs_ex69_variant_r1_r in
  let pb = pbFromList [grs_ex69_variant_r1] in
  pb |> isTerminatingBool |> Printf.printf "[grs_grs_ex69_variant_r1ex69_r1] is terminating : %b";
  ;[%expect{| [grs_grs_ex69_variant_r1ex69_r1] is terminating : true |}]

let print_grs pb = List.iteri 
    (fun i rl -> Printf.printf "rule %d : \n %s" i (rl |> GraphRewritingSystem.toStr_left_interface_right))
    (pb.rules |> GraphRewritingSystem.RuleSet.elements)