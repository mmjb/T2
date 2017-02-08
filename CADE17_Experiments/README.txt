=== Running the experiments

1. Obtain TPDB (e.g., download from http://cl2-informatik.uibk.ac.at/mercurial.cgi/TPDB).
2. Build T2Cert (from this branch, see ../README.txt).
3. Build T2 (from master branch, see ../README.txt).
4. Obtain AProVE (e.g., download from https://github.com/aprove-developers/aprove-releases/releases/tag/aprove-certifiable-2017_05_29).
5. Obtain CeTA (e.g., download from http://cl-informatik.uibk.ac.at/software/ceta/).
6. Fix paths in T2CertHarness.sh, AProVECertHarness.sh, CeTAHarness.sh to the
   corresponding binaries.
7. Run actual experiments:
    $ for f in Integer_Transition_Systems/From_*/*.smt2.t2; do T2CertHarness.sh $f; done | tee T2.log
    $ for f in Integer_Transition_Systems/From_*/*.smt2.inttrs; do AProVECertHarness.sh $f; done | tee AProVE.log
    $ for f in ExperimentLogs/*cert.xml; do CeTAHarness.sh $f; done | tee CeTA.log
8. Generate report website:
    $ python genWebsite.py T2.log AProVE.log CeTA.log ExperimentLogs/ Integer_Transition_Systems/ website/
