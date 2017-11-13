#!/bin/bash

for i in $(seq 1 9); do
    begin='Testcase_'
    outFC='_out_FC.txt'
    outFC=$begin$i$outFC

    outIFC='_out_IFC.txt'
    outIFC=$begin$i$outIFC

    end=".txt"
    fn=$begin$i$end
    # $echo "$fn"
    python3 FOL_FC.py $fn > $outFC
    python3 FOL_IFC.py $fn > $outIFC
done