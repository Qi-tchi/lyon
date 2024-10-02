module Grs = GraphRewritingSystem
module Homo = GraphHomomorphism

type named_grs = {
  grs : Grs.RuleSet.t;
  name : string
}

let fromRulesListAndName rls name = 
  let grs = Grs.RuleSet.of_list rls in
  {grs; name}
let fromRulesSetAndName rls name = 
  {grs=rls; name}
(* type rule_material_t = {
  kvs:int list;
  kes:(int*int*string*int) list;
  lvs:int list;
  les:(int*int*string*int) list; 
  rvs:int list;
  res:(int*int*string*int) list; 
  lhv:(int*int) list;
  lhe:((int*int*string*int) *(int*int*string*int)) list;
  rhv:(int*int) list;
  rhe:((int*int*string*int) *(int*int*string*int)) list;
}  *)
 
(*********************
  Endrullis_2023_example_6.2
*****************************)

let kvs = [1;2]
let kes = []
let lvs = kvs
let les = [(1,"",1,1)]
let lhv = [(1,1);(2,2)]
let lhe = []
let res = [(1,"",2,1)]
let rvs = kvs 
let rhv = lhv
let rhe = []

let endrullis_2023_ex6_2_rule1 =  Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let endrullis_2023_ex6_2_ruleset = Grs.RuleSet.of_list [endrullis_2023_ex6_2_rule1]
let endrullis_2023_ex6_2 = Termination.pbFromList [endrullis_2023_ex6_2_rule1] 

(*********************
  Endrullis_2023_example_6.3
*****************************)

let kvs = [1;2]
let kes = []

let lvs = [1;2;3]
let les = [( 1,"",2,1);(2,"",3,2);(3,"",2,3)]

let lhv = [(1,1);(2,2)]
let lhe = []

let rvs = [1;2;4]
let res =  [(1,"",2,1);(2,"",4,2);(4,"",1,3)]
let rhv = [(1,1);(2,2)]
let rhe = []

let endrullis_2023_ex6_3_rule1 = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let endrullis_2023_ex6_3 =Termination.pbFromList [endrullis_2023_ex6_3_rule1]

  
 (*********************
  Endrullis_2023_example_6.4  
*****************************)
let kvs = [1;2]
let kes = []

let lvs = [1;2]
let les = [(1,"",2,1)]

let lhv = [(1,1);(2,2)]
let lhe = []

let rvs = [1;2;3;4]
let res =  [(1,"",1,1)]

let rhv = [(1,1);(2,2)]
let rhe = []

let endrullis_2023_ex6_4_rule1 = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let endrullis_2023_ex6_4 =Termination.pbFromList [endrullis_2023_ex6_4_rule1] 



(*********************
  Endrullis_2023_example_6.8
*****************************)
let kvs = [1]
let kes = []

let lvs = [1;2]
let les = []
let lhv = [(1,1)]
let lhe = []

let rvs = [1;2]
let res = [(1,"",2,1)]
let rhv = [(1,1)]
let rhe = []

let endrullis202368r1 = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let endrullis202368 =Termination.pbFromList [endrullis202368r1] 

(*********************
  plump_2018_example_3        plump_1995_example_3.8
*****************************)

let kvs = [1;2]
let kes = []

let lvs = [1;2;3]
let les = [(1,"a",2,1);(2,"b",3,2)]

let lhv = [(1,1);(2,2)]
let lhe = []

let rvs = [1;2;3]
let res =  [(1,"a",2,1);(2,"c",3,2)]

let rhv = [(1,1);(2,2)]
let rhe = []
let plump20183r1 =Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let kes = []

let lvs = [1;2;3]
let les = [(1,"c",2,1);(2,"d",3,2)]

let lhv = [(1,1);(2,2)]
let lhe = []

let rvs = [1;2;3]
let res =  [(1,"d",2,1);(2,"b",3,2)]

let rhv = [(1,1);(2,2)]
let rhe = []
let plump20183r2 = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let plump20183 =Termination.pbFromList [plump20183r1; plump20183r2]


(*********************
  plump_2018_fig10
*****************************)

let kvs = [1;2]
let kes = []

let lvs = [1;2]
let les = [(1,"r",1,2);(1,"",2,1);(2,"white",2,3)]

let lhv = [(1,1);(2,2)]
let lhe = []

let rvs = [1;2]
let res =  [(1,"r",1,2);(1,"",2,1);(2,"b",2,3)]

let rhv = [(1,1);(2,2)]
let rhe = []
let plump2018fig10colour1 = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let les = [(1,"r",1,2);(2,"",1,1);(2,"white",2,3)]
let res =  [(1,"r",1,2);(2,"",1,1);(2,"b",2,3)]
let plump2018fig10colour2 = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let les = [(1,"b",1,2);(1,"",2,1);(2,"white",2,3)]
let res =  [(1,"b",1,2);(1,"",2,1);(2,"r",2,3)]
let plump2018fig10colour3 = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let les = [(1,"b",1,2);(2,"",1,1);(2,"white",2,3)]
let res =  [(1,"b",1,2);(2,"",1,1);(2,"r",2,3)]
let plump2018fig10colour4 = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe

let les = [(1,"r",1,2);(1,"",2,1);(2,"r",2,3)]
let res =  [(1,"noire",1,2);(1,"",2,1);(2,"noire",2,3)]
let plump2018fig10invalid1 = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let les = [(1,"b",1,2);(1,"",2,1);(2,"b",2,3)]
let res =  [(1,"noire",1,2);(1,"",2,1);(2,"noire",2,3)]
let plump2018fig10invalid2 = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let les = [(1,"noire",1,2);(2,"r",2,3)]
let res =  [(1,"noire",1,2);(2,"noire",2,3)]
let plump2018fig10invalid3 = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let les = [(1,"noire",1,2);(2,"b",2,3)]
let res =  [(1,"noire",1,2);(2,"noire",2,3)]
let plump2018fig10invalid4 = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe

let les = [(1,"noire",1,2);(2,"white",2,3)]
let res =  [(1,"noire",1,2);(2,"noire",2,3)]
let plump2018fig10propagate = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let plump2018fig10 =Termination.pbFromList 
[plump2018fig10colour1;
 plump2018fig10colour2;
 plump2018fig10colour3;
 plump2018fig10colour4;plump2018fig10invalid1; plump2018fig10invalid2;plump2018fig10invalid3;plump2018fig10invalid4;plump2018fig10propagate ] 

(*********************
  bruggink_2015_example_4
*****************************)
(* eval 100 times
   T 0.1014 / AR   *)
(* let lp1 = [(2,"count",3);(3,"incr",3);(3,"0",1)]
let rp1 = [(2,"count",3);(3,"1",1)]

let lp2 = [(2,"count",1);(3,"incr",3);(3,"1",1)]
let rp2 = [(2,"count",3);(3,"c",1)]

let lp3 = [(2,"c",3);(3,"0",1)]
let rp3 = [(2,"0",3);(3,"1",1)]

let lp4 = [(2,"c",3);(3,"1",1)]
let rp4 = [(2,"0",3);(3,"c",1)]

let bruggink_2015_example_4 = 
  [((lp1,rp1),2);((lp2,rp2),2);((lp3,rp3),2);((lp4,rp4),2)];; *)
(*********************
  bruggink_2015_example_5
*****************************)
(* let bruggink_2015_example_5 =   
  let lp1 = [(2,"count",3) ;(3,"0",1)] in
  let rp1 = [(2,"count",3);(3,"1",1)] in
  let lp2 = [(2,"count",3) ;(3,"1",1)] in
  let rp2 = [(2,"count",3);(3,"c",1)] in
  let lp3 = [(2,"c",3);(3,"0",1)] in
  let rp3 = [(2,"0",3);(3,"1",1)] in
  let lp4 = [(2,"c",3);(3,"1",1)] in
  let rp4 = [(2,"0",3);(3,"c",1)] in
  [((lp1,rp1),2);((lp2,rp2),2);((lp3,rp3),2);((lp4,rp4),2)];; *)
(*********************
  bruggink_2015_example_6
*****************************)
(* let bruggink_2015_example_6 =   
  let lp1 = [(2,"0",1)] in
  let rp1 = [(2,"1",1)] in
  let lp2 = [(2,"1",1)] in
  let rp2 = [(2,"c",1)] in
  let lp3 = [(3,"c",4);(4,"0",1);(4,"0",2)] in
  let rp3 = [(3,"0",4);(4,"1",1);(4,"0",2)] in
  let lp4 = [(3,"c",4);(4,"0",1);(4,"1",2)] in
  let rp4 = [(3,"0",4);(4,"1",1);(4,"1",2)] in
  let lp5 = [(3,"c",4);(4,"1",1);(4,"0",2)] in
  let rp5 = [(3,"0",4);(4,"c",1);(4,"0",2)] in
  let lp6 = [(3,"c",4);(4,"1",1);(4,"1",2)] in
  let rp6 = [(3,"0",4);(4,"c",1);(4,"1",2)] in
  [((lp1,rp1),1);((lp2,rp2),1);((lp3,rp3),3);((lp4,rp4),3);
  ((lp5,rp5),3);((lp6,rp6),3)];; *)

(*********************
  bruggink_2014_example_1
*****************************)
(* let l1 =  [(1,"a",3);(3,"a",2)]
let i1 = 2
let r1 =  [(1,"a",3);(3,"c",3);(3,"a",2)]
let bruggink_2014_example_1 = [((l1,r1),i1)] *)

(*********************
  bruggink_2014_example_4
*****************************)
let bruggink_2014_example_4_l = Homo.fromList
  [1;2] [] 
  [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
  [(1,1);(2,2)] []
let bruggink_2014_example_4_r = Homo.fromList
  [1;2] []
  [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3);]
  [(1,1);(2,2)] []
let bruggink_2014_example_4 = Grs.fromHomos bruggink_2014_example_4_l bruggink_2014_example_4_r
let bruggink_2014_example_4_rl_1 = Grs.fromHomos bruggink_2014_example_4_l bruggink_2014_example_4_r
let bruggink_2014_example_4_named_grs =  {grs = Grs.RuleSet.of_list  [bruggink_2014_example_4]; name = "bruggink_2014_example_4"}
let bruggink_2014_example_4 =Termination.pbFromList [bruggink_2014_example_4]

(*********************
  bruggink_2014_example_5
*****************************)
let l1 =  Homo.fromList 
  [1;2] []  
  [1;3;2] [(1,"0",3,1);(3,"L",2,2)]
  [(1,1);(2,2)] 
  []
let r1 =  
  Homo.fromList 
  [1;2] []  
  [1;2;3;4] [(1,"L",3,1);(3,"1",4,2);(4,"1",2,3)]
  [(1,1);(2,2)] 
  []
let l2 =  Homo.fromList
  [1;2] []  
  [1;3;2]  [(1,"R",3,1);(3,"1",2,2)]
  [(1,1);(2,2)] 
  []
let r2 =  Homo.fromList
  [1;2] []  
  [1;3;2] [(1,"0",3,1);(3,"R",2,2)]
  [(1,1);(2,2)] 
  []
let l3 =   Homo.fromList
  [1;2] []  
  [1;3;2] [(1,"B",3,1);(3,"L",2,2)]
  [(1,1);(2,2)] 
  []
let r3 =  Homo.fromList
  [1;2] []  
  [1;3;2] [(1,"R",2,1)]
  [(1,1);(2,2)] 
  []
let l4 =  Homo.fromList
  [1;2] []  
  [1;3;2] [(1,"R",3,1);(3,"B",2,2)]
  [(1,1);(2,2)] 
  []
let r4 =  Homo.fromList
  [1;2] []  
  [1;3;2] [(1,"L",3,1);(3,"B",2,2)]
  [(1,1);(2,2)] 
  []
let bruggink_2014_example_5_rl1 = Grs.fromHomos l1 r1
let bruggink_2014_example_5_rl2 = Grs.fromHomos l2 r2
let bruggink_2014_example_5_rl3 = Grs.fromHomos l3 r3
let bruggink_2014_example_5_rl4 = Grs.fromHomos l4 r4
let bruggink_2014_example_5 = 
  [bruggink_2014_example_5_rl1;bruggink_2014_example_5_rl2;bruggink_2014_example_5_rl3;bruggink_2014_example_5_rl4]
let bruggink_2014_example_5_named = fromRulesListAndName bruggink_2014_example_5 "bruggink_2014_ex5"
(*********************
  bruggink_2014_example_6 ??? quelle est la diff avec example 4
*****************************)

(*********************
exemple  : ad-hoc routing protocol
*****************************)
(* let sml = [(1,"M",1); (1,"C",2);(2,"U",2)]@[(1,"node",1);(2,"node",2)];;
let smr = [(1,"C",2);(2,"M",2)]@[(1,"node",1);(2,"node",2)];;
let arl = [(1,"S",1); (1,"C",2);(2,"S",2)]@[(1,"node",1);(2,"node",2)];;
let arr = [(1,"S",1);(1,"C",3);(3,"R",3);(3,"U",3);(3,"C",2);(2,"S",2)]
          @[(1,"node",1);(2,"node",2);(3,"node",3)];;
let cil = [(2,"S",2);(2,"U",2)]@[(1,"node",1);(2,"node",2)];;
let cir = [(1,"C",2);(2,"S",2);(2,"U",2)]@[(1,"node",1);(2,"node",2)];;
 
let routing = [((sml,smr),2);((arl,arr),2);((cil,cir),1)];; *)


(*********************
exemple  : bonfante_2023_main_example_follow
*****************************)
let kvs = [1;2;3]
let kes = []

let lvs = [1;2;3]
let les = [(1,"T",2,1);(2,"a",3,2)]

let lhv = [(1,1);(2,2);(3,3)]
let lhe = []

let rvs = [1;2;3]
let res = [(1,"T",3,1);(2,"a",3,2)]

let rhv = [(1,1);(2,2);(3,3)]
let rhe = []

let bonfante_2023_main_example_follow = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let bonfante_2023_main_example =Termination.pbFromList [bonfante_2023_main_example_follow]  

(* endrullis ex 6.9 *)
let grs_ex69_r1_r = Homo.fromList 
  [1;2;3] [(1,"s",3,1);(3,"0",3,2)]
  [1;2;3;4] [(1,"s",3,1);(3,"0",3,2); (2,"s",4,3); (4,"0",4,4)]
  [(1,1);(2,2);(3,3)] 
  [(1,1); (2,2)]
 
let grs_ex69_r1_l = Homo.fromList 
  [1;2;3] [(1,"s",3,1);(3,"0",3,2)]
  [1;2;3] [(1,"s",3,1);(3,"0",3,2); (2,"s",3,3)]
  [(1,1);(2,2);(3,3)] 
  [(1,1); (2,2)]

let grs_ex69_r1 = Grs.fromHomos grs_ex69_r1_l grs_ex69_r1_r
let grs_ex69 = Termination.pbFromList [grs_ex69_r1]

(* endrullis ex 6.9 variant *)
let grs_ex69_variant_r1_r = Homo.fromList 
  [1;2;3] []
  [1;2;3;4;5] [(1,"s",3,1);(3,"0",3,2); (2,"s",4,3); (4,"0",4,4);
   (5,"0",5,5); (5,"0",5,6); (5,"0",5,7)]
  [(1,1);(2,2);(3,3)] 
  []

let grs_ex69_variant_r1_l = Homo.fromList 
  [1;2;3] []
  [1;2;3] [(1,"s",3,1);(3,"0",3,2); (2,"s",3,3)]
  [(1,1);(2,2);(3,3)] 
  []

let grs_ex69_variant_r1 = Grs.fromHomos grs_ex69_variant_r1_l grs_ex69_variant_r1_r
let grs_ex69_variant = Termination.pbFromList [grs_ex69_variant_r1]

(**************) 
(* let metivier_1995_majAB = Grs.fromGls ConcretGraphRelabelingSystem.metivier_1995_majAB

let metivier_1995_majAB_named = fromRulesSetAndName metivier_1995_majAB "majAB" *)