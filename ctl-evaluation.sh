#!/bin/bash

TIMELIMIT=60

declare -a EXAMPLES
EXAMPLES[1]='[AG](varA != 1 || [AF](varR == 1))'
EXAMPLES[2]='[EF](varA == 1 && [EG](varR != 5))'
EXAMPLES[3]='[AG](varA != 1 || [EF](varR == 1))'
EXAMPLES[4]='[EF](varA == 1 && [AG](varR != 1))'
EXAMPLES[5]='[AG](varS != 1 || [AF](varU == 1))'
EXAMPLES[6]='[EF](varS == 1 || [EG](varU != 1))'
EXAMPLES[7]='[AG](varS != 1 || [EF](varU == 1))'
EXAMPLES[8]='[EF](varS == 1 && [AG](varU != 1))'
EXAMPLES[9]='[AG](varA != 1 || [AF](varR == 1))'
EXAMPLES[10]='[EF](varA == 1 && [EG](varR != 1))'
EXAMPLES[11]='[AG](varA != 1 || [EF](varR == 1))'
EXAMPLES[12]='[EF](varA == 1 && [AG](varR != 1))'
EXAMPLES[13]='[EG](varP1 != 1) || [EG](varP2 != 1)'
EXAMPLES[14]='[EG](varP1 != 1) || [EG](varP2 != 1)'
EXAMPLES[15]='[EF](varP1 == 1) && [EF](varP2 == 1)'
EXAMPLES[16]='[AG](varP1 != 1) || [AG](varP2 != 1)'
EXAMPLES[17]='[AG]([AF](varW >= 1))'
EXAMPLES[18]='[EF]([EG](varW < 1))'
EXAMPLES[19]='[AG]([EF](varW >=1))'
EXAMPLES[20]='[EF]([AG](varW < 1))'
EXAMPLES[21]='[AG]([AF](varW == 1))'
EXAMPLES[22]='[EF]([EG](varW != 1))'
EXAMPLES[23]='[AG]([EF](varW == 1))'
EXAMPLES[24]='[EF]([AG](varW != 1))'
EXAMPLES[25]='(varC <= 5) || ([AF](varR > 5))'
EXAMPLES[26]='(varC > 5) && [EG](varR <= 5)'
EXAMPLES[27]='(varC <= 5) || [EF](varR > 5)'
EXAMPLES[28]='(varC > 5) && [AG](varR <= 5)'

BEGIN_TIME=`date +%s`
for IDX in `seq 1 28`; do
    PROP=${EXAMPLES[$IDX]}
    FILE=test/cav13-ctl-examples/P${IDX}.t2
    echo "Checking phi='${PROP}' on P${IDX}"
    
    echo -n "  Check for phi: "
    echo "Result of src/bin/Release/T2.exe -CTL \"${PROP}\" -log -input_t2 \"${FILE}\"" > ${FILE}.pos.log
    OUTPUT=`(time src/bin/Release/T2.exe -CTL "${PROP}" -log -input_t2 "${FILE}" >> ${FILE}.pos.log) 2>&1`
    TIME_POS=`echo "$OUTPUT" | grep "^real" | perl -pe 's/^real\s+(\d+)m(\d+)\.(\d+)s\$/(\$1*60+\$2)*1000+\$3/e'`
    if `grep -q "Temporal proof succeeded" ${FILE}.pos.log`; then 
        echo -n "Success"
    elif `grep -q "Temporal proof failed" ${FILE}.pos.log`; then 
        echo -n "Failed"
    else
        echo -n "CRASH"
    fi
    echo " (in" `printf "%i" "$TIME_POS"` "ms)"

    echo -n "  Check for !phi: "
    echo "Result of src/bin/Release/T2.exe -CTL \"!(${PROP})\" -log -input_t2 \"${FILE}\"" > ${FILE}.neg.log
    OUTPUT=`(time src/bin/Release/T2.exe -CTL "!(${PROP})" -log -input_t2 "${FILE}" >> ${FILE}.neg.log) 2>&1`
    TIME_NEG=`echo "$OUTPUT" | grep "^real" | perl -pe 's/^real\s+(\d+)m(\d+)\.(\d+)s\$/(\$1*60+\$2)*1000+\$3/e'`
    if `grep -q "Temporal proof succeeded" ${FILE}.neg.log`; then 
        echo -n "Success"
    elif `grep -q "Temporal proof failed" ${FILE}.neg.log`; then 
        echo -n "Failed"
    else
        echo -n "CRASH"
    fi
    echo " (in" `printf "%i" "$TIME_NEG"` "ms)"
done

END_TIME=`date +%s`
TOTAL_TIME=$(( END_TIME-BEGIN_TIME ))

echo
echo "Total time:" `printf "%'8.2f" "${TOTAL_TIME}"` "seconds"
