#!/bin/bash
BASE_DIR=$(dirname $(realpath ${0}))

LOG_PATH="${BASE_DIR}/T2CertLogs/"
mkdir -p "${LOG_PATH}"

T2FULL_PATH="${BASE_DIR}/../T2/src/bin/Release/T2.exe"
T2CERT_PATH="${BASE_DIR}/src/bin/Release/T2.exe"
T2_TIMEOUT=10

CETA_PATH="${BASE_DIR}/../cetaITS/Main.exe"
CETA_TIMEOUT=10

EX_PATH=$1
EX_WINPATH=$(cygpath -w "${EX_PATH}")
EX_NAME=$(echo $1 | sed -e 's!/!__!g')

#Step 1: Run T2 on example
CERT_PATH="${LOG_PATH}/${EX_NAME}.cert.xml"
CERT_WINPATH=$(cygpath -w "${CERT_PATH}")
T2_LOG="${LOG_PATH}/${EX_NAME}.T2.log"
T2_ERRLOG="${LOG_PATH}/${EX_NAME}.T2.errlog"
(time timeout "${T2_TIMEOUT}s" "${T2CERT_PATH}" --termination --try_nonterm false --export_cert "${CERT_WINPATH}" --input_t2 "${EX_WINPATH}" --log --print_proof 1> "${T2_LOG}") &> "${T2_ERRLOG}"
T2_RUNTIME=$(perl -le 'my $t=0; while(<>){chomp; if (/real\s+(\d+)m(\d+\.\d+)s/) { $t = 60 * $1 + $2 } } print "${t}"' < "${T2_ERRLOG}")



#Step 2: Check if it's terminating
if [[ $(tail -n 1 ${T2_LOG}) =~ "Termination proof succeeded" ]]; then
    #Step 3: Check if certificate goes through:
    CETA_LOG="${LOG_PATH}/${EX_NAME}.ceta.log"
    CETA_ERRLOG="${LOG_PATH}/${EX_NAME}.ceta.errlog"
    (time timeout "${CETA_TIMEOUT}s" "${CETA_PATH}" "${CERT_WINPATH}" 1> "${CETA_LOG}") &> "${CETA_ERRLOG}"
    CETA_RUNTIME=$(perl -le 'my $t=0; while(<>){chomp; if (/real\s+(\d+)m(\d+\.\d+)s/) { $t = 60 * $1 + $2 } } print "${t}"' < "${CETA_ERRLOG}")

    if [[ $(tail -n 1 ${CETA_LOG}) =~ "CERTIFIED" ]]; then
        echo "${EX_PATH}: TERMINATING (${T2_RUNTIME}s) -- CERTIFIED (${CETA_RUNTIME}s)"
    else
        echo "${EX_PATH}: TERMINATING (${T2_RUNTIME}s) -- REJECTED  (${CETA_RUNTIME}s)"
    fi
else
    T2FULL_LOG="${LOG_PATH}/${EX_NAME}.T2Full.log"
    T2FULL_ERRLOG="${LOG_PATH}/${EX_NAME}.T2Full.errlog"
    (time timeout "${T2_TIMEOUT}s" "${T2FULL_PATH}" --termination --try_nonterm false --input_t2 "${EX_WINPATH}" --log --print_proof 1> "${T2FULL_LOG}") &> "${T2FULL_ERRLOG}"
    T2FULL_RUNTIME=$(perl -le 'my $t=0; while(<>){chomp; if (/real\s+(\d+)m(\d+\.\d+)s/) { $t = 60 * $1 + $2 } } print "${t}"' < "${T2FULL_ERRLOG}")

    if [[ $(tail -n 1 ${T2FULL_LOG}) =~ "Termination proof succeeded" ]]; then
        echo "${EX_PATH}: UNKNOWN (${T2_RUNTIME}s) ## FULL TERMINATING (${T2FULL_RUNTIME}s)"
    else
        echo "${EX_PATH}: UNKNOWN (${T2_RUNTIME}s) ## FULL UNKNOWN (${T2FULL_RUNTIME}s)"
    fi
fi
