#!/bin/bash
BASE_DIR=$(dirname $(realpath ${0}))

LOG_PATH="${BASE_DIR}/ExperimentLogs/"
mkdir -p "${LOG_PATH}"

T2_FULL_PATH="${BASE_DIR}/../../T2/src/bin/Release/T2.exe"
T2_CERT_PATH="${BASE_DIR}/../src/bin/Release/T2.exe"
T2_TIMEOUT=120

EX_PATH=$1
EX_WINPATH=$(cygpath -w "${EX_PATH}")
EX_NAME=$(echo $1 | sed -e 's!/!__!g')

CERT_PATH="${LOG_PATH}/${EX_NAME}.cert.xml"
CERT_WINPATH=$(cygpath -w "${CERT_PATH}")
HINTING_CERT_PATH="${LOG_PATH}/${EX_NAME}.hinting_cert.xml"
HINTING_CERT_WINPATH=$(cygpath -w "${HINTING_CERT_PATH}")

#Step 1a: Run T2Cert on example
T2_CERT_LOG="${LOG_PATH}/${EX_NAME}.T2Cert.log"
T2_CERT_ERRLOG="${LOG_PATH}/${EX_NAME}.T2Cert.errlog"
(time timeout "${T2_TIMEOUT}s" "${T2_CERT_PATH}" --termination --try_nonterm false --export_cert "${CERT_WINPATH}" --input_t2 "${EX_WINPATH}" --log --print_proof 1> "${T2_CERT_LOG}") &> "${T2_CERT_ERRLOG}"
T2_CERT_RUNTIME=$(perl -le 'my $t=0; while(<>){chomp; if (/real\s+(\d+)m(\d+\.\d+)s/) { $t = 60 * $1 + $2 } } print "${t}"' < "${T2_CERT_ERRLOG}")
T2_CERT_RESULT="MAYBE"
if grep -q "Termination proof succeeded" "${T2_CERT_LOG}"; then
    T2_CERT_RESULT="YES"
fi

#Step 2: Run T2Cert with hints on example
T2_HINTING_CERT_LOG="${LOG_PATH}/${EX_NAME}.T2HintingCert.log"
T2_HINTING_CERT_ERRLOG="${LOG_PATH}/${EX_NAME}.T2HintingCert.errlog"
(time timeout "${T2_TIMEOUT}s" "${T2_CERT_PATH}" --termination --try_nonterm false --export_cert "${HINTING_CERT_WINPATH}" --input_t2 "${EX_WINPATH}" --export_cert_hints --log --print_proof 1> "${T2_HINTING_CERT_LOG}") &> "${T2_HINTING_CERT_ERRLOG}"
T2_HINTING_CERT_RUNTIME=$(perl -le 'my $t=0; while(<>){chomp; if (/real\s+(\d+)m(\d+\.\d+)s/) { $t = 60 * $1 + $2 } } print "${t}"' < "${T2_HINTING_CERT_ERRLOG}")
T2_HINTING_CERT_RESULT="MAYBE"
if grep -q "Termination proof succeeded" "${T2_HINTING_CERT_LOG}"; then
    T2_HINTING_CERT_RESULT="YES"
fi

#Step 3: Run T2 on example:
T2_FULL_LOG="${LOG_PATH}/${EX_NAME}.T2Full.log"
T2_FULL_ERRLOG="${LOG_PATH}/${EX_NAME}.T2Full.errlog"
(time timeout "${T2_TIMEOUT}s" "${T2_FULL_PATH}" --termination --input_t2 "${EX_WINPATH}" --log --print_proof 1> "${T2_FULL_LOG}") &> "${T2_FULL_ERRLOG}"
T2_FULL_RUNTIME=$(perl -le 'my $t=0; while(<>){chomp; if (/real\s+(\d+)m(\d+\.\d+)s/) { $t = 60 * $1 + $2 } } print "${t}"' < "${T2_FULL_ERRLOG}")
T2_FULL_RESULT="MAYBE"
if grep -q "Termination proof succeeded" "${T2_FULL_LOG}"; then
    T2_FULL_RESULT="YES"
elif grep -q "Nontermination proof succeeded" "${T2_FULL_LOG}"; then
    T2_FULL_RESULT="NO"
fi
T2_FULL_FEATURES=""
if grep -q "Found lexicographic polyranking function" "${T2_FULL_LOG}"; then
    T2_FULL_FEATURES="POLYRANKING ${T2_FULL_FEATURES}"
fi

if grep -q "Trying the unrolling technique." "${T2_FULL_LOG}"; then
    T2_FULL_FEATURES="UNROLLING ${T2_FULL_FEATURES}"
fi

if grep -q "Trying initial condition detection." "${T2_FULL_LOG}"; then
    T2_FULL_FEATURES="INITIALCOND ${T2_FULL_FEATURES}"
fi

echo "${EX_PATH};${T2_CERT_RESULT};${T2_CERT_RUNTIME};${CERT_WINPATH};${T2_HINTING_CERT_RESULT};${T2_HINTING_CERT_RUNTIME};${HINTING_CERT_WINPATH};${T2_FULL_RESULT};${T2_FULL_RUNTIME};${T2_FULL_FEATURES}"
