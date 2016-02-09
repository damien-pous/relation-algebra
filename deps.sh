#!/bin/bash

FILES=*.v
FILES=${FILES#tests_*.v}

(
    echo "digraph RelationAlgebra { size=\"8,10\" ";
    for i in $FILES; do echo ${i/.v/} "["URL=\"html/RelationAlgebra.${i/.v/.html}\" "];"; done
    coqdep $FILES | grep -v vio | sed -E "s/tests_[^ ]*//g;s/[^ ]*.(glob|beautified|v|cmo|cma|cmxs)[[:>:]]//g;s/.vo//g;s/:/ ->/g" | \
    while read line; do echo -n $line; echo " ;" ; done;
    echo "}";
) | sed "s/ -> ;/;/g" | sed "s/-> \(.*\) ;/-> {\1};/g" |tred > deps.dat 

dot -Tcmapx -odeps.map -Tjpg -odeps.jpg deps.dat
#-Tpdf -odeps.pdf 
