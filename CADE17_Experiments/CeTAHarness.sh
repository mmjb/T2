#!/bin/bash
BASE_DIR=$(dirname $(realpath ${0}))

LOG_PATH="${BASE_DIR}/ExperimentLogs/"
mkdir -p "${LOG_PATH}"

CETA_PATH="${BASE_DIR}/../../cetaITS/Main.exe"
CETA_TIMEOUT=300

CERT_PATH=$1
CERT_WINPATH=$(cygpath -w "${CERT_PATH}")

#Step 3: If we have a certificate, run ceta:
CETA_LOG="${LOG_PATH}/${CERT_PATH}.ceta.log"
CETA_ERRLOG="${LOG_PATH}/${CERT_PATH}.ceta.errlog"
(time timeout "${CETA_TIMEOUT}s" "${CETA_PATH}" "${CERT_WINPATH}" 1> "${CETA_LOG}") &> "${CETA_ERRLOG}"
CETA_RUNTIME=$(perl -le 'my $t=0; while(<>){chomp; if (/real\s+(\d+)m(\d+\.\d+)s/) { $t = 60 * $1 + $2 } } print "${t}"' < "${CETA_ERRLOG}")

if [[ $(tail -n 1 ${CETA_LOG}) =~ "CERTIFIED" ]]; then
    CETA_RESULT="CERTIFIED"
elif grep -q "REJECTED" "${CETA_LOG}"; then
    CETA_RESULT="REJECTED"
else
    CETA_RESULT="CETA ERROR"
fi

echo "${CERT_PATH};${CERT_WINPATH};${CETA_RESULT};${CETA_RUNTIME}"
