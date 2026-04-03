SHELL    = /bin/bash
CXX      = g++
CXXFLAGS = -std=c++17 -O2
SRCDIR   = data struct

.PHONY: all test test-quick test-lake clean

# ── Build ────────────────────────────────────────────────────────────────────
all: simplify

simplify:
	$(CXX) $(CXXFLAGS) -o simplify "$(SRCDIR)/Simplify.cpp"

# ── Run ALL 15 tests ─────────────────────────────────────────────────────────
# PASS criteria (matching the grader):
#   1. area_in == area_out  (area preserved)
#   2. my_verts <= exp_verts (didn't stop earlier than reference)
#      (if target is unachievable the reference already reflects the minimum)
# "EXACT" means byte-for-byte match with reference output.
test: simplify
	@echo ""; \
	echo "======================================================"; \
	echo " Test results  (PASS = area ok + verts <= reference)"; \
	echo "======================================================"; \
	pass=0; fail=0; exact=0; \
	run() { \
		input=$$1; target=$$2; \
		expected="$${input/input_/output_}"; expected="$${expected/.csv/.txt}"; \
		actual=$$(./simplify "$$input" $$target 2>/dev/null); \
		my_verts=$$(echo  "$$actual"  | grep -c '^[0-9]'); \
		exp_verts=$$(grep -c '^[0-9]' "$$expected"); \
		area_in=$$(echo  "$$actual" | grep 'signed area in input'  | awk '{print $$NF}'); \
		area_out=$$(echo "$$actual" | grep 'signed area in output' | awk '{print $$NF}'); \
		my_disp=$$(echo  "$$actual" | grep 'areal displacement'    | awk '{print $$NF}'); \
		exp_disp=$$(grep  'areal displacement' "$$expected"         | awk '{print $$NF}'); \
		area_ok=1; [ "$$area_in" != "$$area_out" ] && area_ok=0; \
		verts_ok=1; [ "$$my_verts" -gt "$$exp_verts" ] && verts_ok=0; \
		note=""; \
		[ "$$area_ok"  = "0" ] && note="$${note}[AREA_MISMATCH]"; \
		[ "$$verts_ok" = "0" ] && note="$${note}[TOO_MANY_VERTS:$$my_verts>$$exp_verts]"; \
		if [ "$$area_ok" = "1" ] && [ "$$verts_ok" = "1" ]; then \
			pass=$$((pass+1)); status="PASS"; \
		else \
			fail=$$((fail+1)); status="FAIL"; \
		fi; \
		if diff -q <(echo "$$actual") "$$expected" > /dev/null 2>&1; then \
			exact=$$((exact+1)); note="$$note [exact]"; \
		fi; \
		printf "%-5s %-42s v=%s/%s  disp=%s ref=%s%s\n" \
			"$$status" "$$input" "$$my_verts" "$$exp_verts" "$$my_disp" "$$exp_disp" "$$note"; \
	}; \
	run input_rectangle_with_two_holes.csv   7; \
	run input_cushion_with_hexagonal_hole.csv 13; \
	run input_blob_with_two_holes.csv        17; \
	run input_wavy_with_three_holes.csv      21; \
	run input_lake_with_two_islands.csv      17; \
	run input_original_01.csv  99; \
	run input_original_02.csv  99; \
	run input_original_03.csv  99; \
	run input_original_04.csv  99; \
	run input_original_05.csv  99; \
	run input_original_06.csv  99; \
	run input_original_07.csv  99; \
	run input_original_08.csv  99; \
	run input_original_09.csv  99; \
	run input_original_10.csv  99; \
	echo ""; \
	echo "------------------------------------------------------"; \
	printf " Passed: %d/15    Exact match: %d/15\n" "$$pass" "$$exact"; \
	echo "======================================================"

# ── Quick test: only the 5 polygon-with-holes cases (fast) ───────────────────
test-quick: simplify
	@echo ""; \
	echo "======================================================"; \
	echo " Quick test (5 polygon-with-holes cases)"; \
	echo "======================================================"; \
	pass=0; fail=0; \
	run() { \
		input=$$1; target=$$2; \
		expected="$${input/input_/output_}"; expected="$${expected/.csv/.txt}"; \
		actual=$$(./simplify "$$input" $$target 2>/dev/null); \
		my_verts=$$(echo  "$$actual"  | grep -c '^[0-9]'); \
		exp_verts=$$(grep -c '^[0-9]' "$$expected"); \
		area_in=$$(echo  "$$actual" | grep 'signed area in input'  | awk '{print $$NF}'); \
		area_out=$$(echo "$$actual" | grep 'signed area in output' | awk '{print $$NF}'); \
		my_disp=$$(echo  "$$actual" | grep 'areal displacement'    | awk '{print $$NF}'); \
		exp_disp=$$(grep  'areal displacement' "$$expected"         | awk '{print $$NF}'); \
		area_ok=1; [ "$$area_in" != "$$area_out" ] && area_ok=0; \
		verts_ok=1; [ "$$my_verts" -gt "$$exp_verts" ] && verts_ok=0; \
		note=""; \
		[ "$$area_ok"  = "0" ] && note="  !! area_in=$$area_in area_out=$$area_out"; \
		[ "$$verts_ok" = "0" ] && note="$${note}  !! verts $$my_verts > ref $$exp_verts"; \
		if [ "$$area_ok" = "1" ] && [ "$$verts_ok" = "1" ]; then \
			pass=$$((pass+1)); status="PASS"; \
		else \
			fail=$$((fail+1)); status="FAIL"; \
		fi; \
		printf "%-5s %-42s v=%s/%s  disp=%s ref=%s%s\n" \
			"$$status" "$$input" "$$my_verts" "$$exp_verts" "$$my_disp" "$$exp_disp" "$$note"; \
	}; \
	run input_rectangle_with_two_holes.csv   7; \
	run input_cushion_with_hexagonal_hole.csv 13; \
	run input_blob_with_two_holes.csv        17; \
	run input_wavy_with_three_holes.csv      21; \
	run input_lake_with_two_islands.csv      17; \
	echo ""; \
	printf " Passed: %d/5\n" "$$pass"; \
	echo "======================================================"

# ── Test only the 10 large lake cases ────────────────────────────────────────
test-lake: simplify
	@echo ""; \
	echo "======================================================"; \
	echo " Lake tests (10 single-ring cases, target=99)"; \
	echo "======================================================"; \
	pass=0; fail=0; \
	run() { \
		input=$$1; \
		expected="$${input/input_/output_}"; expected="$${expected/.csv/.txt}"; \
		actual=$$(./simplify "$$input" 99 2>/dev/null); \
		my_verts=$$(echo  "$$actual"  | grep -c '^[0-9]'); \
		exp_verts=$$(grep -c '^[0-9]' "$$expected"); \
		area_in=$$(echo  "$$actual" | grep 'signed area in input'  | awk '{print $$NF}'); \
		area_out=$$(echo "$$actual" | grep 'signed area in output' | awk '{print $$NF}'); \
		my_disp=$$(echo  "$$actual" | grep 'areal displacement'    | awk '{print $$NF}'); \
		exp_disp=$$(grep  'areal displacement' "$$expected"         | awk '{print $$NF}'); \
		area_ok=1; [ "$$area_in" != "$$area_out" ] && area_ok=0; \
		verts_ok=1; [ "$$my_verts" -gt "$$exp_verts" ] && verts_ok=0; \
		note=""; \
		[ "$$area_ok"  = "0" ] && note="  !! AREA_MISMATCH"; \
		[ "$$verts_ok" = "0" ] && note="$${note}  !! verts $$my_verts > ref $$exp_verts"; \
		if [ "$$area_ok" = "1" ] && [ "$$verts_ok" = "1" ]; then \
			pass=$$((pass+1)); status="PASS"; \
		else \
			fail=$$((fail+1)); status="FAIL"; \
		fi; \
		printf "%-5s %-30s  v=%s/%s  disp=%s ref=%s%s\n" \
			"$$status" "$$input" "$$my_verts" "$$exp_verts" "$$my_disp" "$$exp_disp" "$$note"; \
	}; \
	for i in 01 02 03 04 05 06 07 08 09 10; do \
		run "input_original_$${i}.csv"; \
	done; \
	echo ""; \
	printf " Passed: %d/10\n" "$$pass"; \
	echo "======================================================"

# ── Run one specific test and show full diff ──────────────────────────────────
# Usage:  make run FILE=input_blob_with_two_holes.csv TARGET=17
run: simplify
	@input="$(FILE)"; target="$(TARGET)"; \
	expected="$${input/input_/output_}"; expected="$${expected/.csv/.txt}"; \
	echo "--- Your output ---"; \
	./simplify "$$input" $$target 2>/dev/null | tee /tmp/_actual.txt; \
	echo ""; \
	echo "--- Diff (< yours  > expected) ---"; \
	diff /tmp/_actual.txt "$$expected" || true

# ── Clean ─────────────────────────────────────────────────────────────────────
clean:
	rm -f simplify
