#!/bin/bash
BASE_DIR=$(dirname $(realpath ${0}))

LOG_PATH="${BASE_DIR}/ExperimentLogs/"
mkdir -p "${LOG_PATH}"

APROVE_PATH="aprove-cd120c4c18b0fc86b174897fb19c2ce76c2da679.jar"
APROVE_TIMEOUT=120

EX_PATH=$1
EX_WINPATH=$(cygpath -w "${EX_PATH}")
EX_NAME=$(echo $1 | sed -e 's!/!__!g')

CERT_PATH="${LOG_PATH}/${EX_NAME}.aprove.cert.xml"
CERT_WINPATH=$(cygpath -w "${CERT_PATH}")

#Step 1: Run AProVE (certified) on example
APROVE_CERT_OUT="${LOG_PATH}/${EX_NAME}.AProVECert.output"
APROVE_CERT_ERRLOG="${LOG_PATH}/${EX_NAME}.AProVECert.errlog"
(time timeout "${APROVE_TIMEOUT}s" java -Xmx4000m -jar "${APROVE_PATH}" -p cpf -C ceta -m wst -t "${APROVE_TIMEOUT}" "${EX_WINPATH}" 1> "${APROVE_CERT_OUT}") &> "${APROVE_CERT_ERRLOG}"
APROVE_CERT_RUNTIME=$(perl -le 'my $t=0; while(<>){chomp; if (/real\s+(\d+)m(\d+\.\d+)s/) { $t = 60 * $1 + $2 } } print "${t}"' < "${APROVE_CERT_ERRLOG}")
APROVE_CERT_RESULT="MAYBE"
if head -n 1 "${APROVE_CERT_OUT}" | grep -q "^YES$"; then
    APROVE_CERT_RESULT="YES"
    tail -n +2 "${APROVE_CERT_OUT}" > "${CERT_PATH}"
fi  
    
#Step 2: Run AProVE (full) on example:
APROVE_FULL_OUT="${LOG_PATH}/${EX_NAME}.AProVEFull.output"
APROVE_FULL_HTMLPROOF="${LOG_PATH}/${EX_NAME}.AProVEFull.proof"
APROVE_FULL_ERRLOG="${LOG_PATH}/${EX_NAME}.AProVEFull.errlog"
(time timeout "${APROVE_TIMEOUT}s" java -Xmx4000m -jar "${APROVE_PATH}" -p html -m wst -t "${APROVE_TIMEOUT}" "${EX_WINPATH}" 1> "${APROVE_FULL_OUT}") &> "${APROVE_FULL_ERRLOG}"
APROVE_FULL_RUNTIME=$(perl -le 'my $t=0; while(<>){chomp; if (/real\s+(\d+)m(\d+\.\d+)s/) { $t = 60 * $1 + $2 } } print "${t}"' < "${APROVE_FULL_ERRLOG}")
APROVE_FULL_RESULT="MAYBE"
if head -n 1 "${APROVE_FULL_OUT}" | grep -q "^YES$"; then
    APROVE_FULL_RESULT="YES"
#    tail -n +2 "${APROVE_FULL_OUT}" > "${APROVE_FULL_HTMLPROOF}"
elif head -n 1 "${APROVE_FULL_OUT}" | grep -q "^NO$"; then
    APROVE_FULL_RESULT="NO"
#    tail -n +2 "${APROVE_FULL_OUT}" > "${APROVE_FULL_HTMLPROOF}"    
fi

echo "${EX_PATH};${APROVE_CERT_RESULT};${APROVE_CERT_RUNTIME};${CERT_WINPATH};${APROVE_FULL_RESULT};${APROVE_FULL_RUNTIME}"
