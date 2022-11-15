I've included 2 tests here to show you how the tool runs/works.

Test 1: miniProof_polishnotation_1.opb/pbp
 - This test was taken directly from Dr. Gocht's VeriPB/tests/integration_tests/correct directory.

This can be run with the following command:
python3 pbp2pbip.py --opb_file pbp2pbip-tests/miniProof/miniProof_polishnotation_1.opb --pbp_file pbp2pbip-tests/miniProof/miniProof_polishnotation_1.pbp

Test 2: php.opb/pbp
 - Found this example from the following set of slides: https://sat-smt-ws.gitlab.io/2019/assets/slides/daniel1.pdf
 - I did copy the formula and I handwrote the proof (which was then checked by VeriPB), and my tool was handily able to generate a PBIP proof.

This can be run with the following command:
python3 pbp2pbip.py --opb_file pbp2pbip-tests/php/php.opb --pbp_file pbp2pbip-tests/php/php.veripb


