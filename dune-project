(lang dune 3.15)

(name lyon)

(generate_opam_files true)

(source
 (github Qi-tchi/lyon))

(authors "Qi QIU")

(maintainers "Qi QIU")

(license "MIT")   

(documentation "https://github.com/Qi-tchi/lyon#readme")   

(package
 (name lyon)
 (synopsis "A comprehensive framework for analyzing termination in graph rewriting systems")  
 (description "This project enhances termination analysis for arrow-labeled multigraph rewriting systems by building on the techniques developed by Bruggink et al. and Endrullis et al. It introduces a machine-checkable condition that accounts for multiple edges, addressing limitations of previous methods and simplifying termination proofs.")   
 (depends ocaml dune)
 (tags
  (topics "Graph Rewriting" "Termination Analysis" "OCaml" "Formal Methods"))   
)
