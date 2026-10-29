# Palomar mechanical verification

The collection has seven independent configurations. A local Comparator check and the current full Palomar workflow are separate checks. Neither is an editorial decision or a registration.

## Current official references

The inspected [policy](https://github.com/PalomarRegistry/PalomarPolicy/tree/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60), [template](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406), and [full verifier](https://github.com/PalomarRegistry/PalomarSubmission/tree/c02bbeaed888df45c4e28c4e99dba540ad21552a) were current public revisions on 26 October 2026. The v0.4 schema revision is `99c678e569c7c4c0772db297c5ddd5e4c9b6322e`.

The policy and template differ on some details. The metadata uses the conservative source categories `paper` and `other`, which satisfy both. The current verifier uses the submitted Lean toolchain for Comparator and NanoDa. For Lean 4.35 it selects con-ron from Lean 4.36.0-rc1, commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`, with authenticated archive and executable hashes. The local template script uses the bundled 4.35 con-ron instead. No submitted configuration has an external-kernel exemption.

## Full workflow

The [manual workflow](../.github/workflows/palomar-preflight.yml) calls the exact official reusable workflow at revision `c02bbeaed888df45c4e28c4e99dba540ad21552a`. It uses `mode: full` and `palomar-standard-v1`. It has read-only repository permissions and inherits no secrets. Each family has a separate job. It creates ordinary Actions report artifacts. It does not call the Palomar intake API, register a result, create a tag, or create a release.

The official profile requires Linux x86_64, at least 14 GiB effective memory, and 20 GiB free workspace. The local Linux ARM64 kernel checks do not claim this profile. The full workflow authenticates dependencies, compiles the Challenge under a protected module identity, confines the Solution build, compares statements and proof exports, and runs the selected proof checkers.

Use the [Actions run list](https://github.com/dvgyl/math-and-theory/actions/workflows/palomar-preflight.yml) to find full-run reports. Dispatch the workflow at the intended source revision. Check the actual Actions `head_sha`. Download each `mechanical-report-<request_id>` artifact. Its report must identify the intended commit, paths, configuration, and pipeline revision. Read its final status and every kernel outcome. A preparation step alone is not a full pass. A report for one commit does not certify a later proof change.

## Submission fields

Each future submission uses repository `https://github.com/dvgyl/math-and-theory`, a full published 40-character commit, project path `lean`, metadata path `lean/formalization.yaml`, and one repository-relative configuration path `lean/comparator/<discipline>/<family>.json`. The human submitter relationship is `I am a responsible author or maintainer`.

The [catalogue](../CONTENTS.md) gives the family identifiers. No Palomar submission has been made. Research interest, attribution, statement review, and registration remain separate from mechanical verification.
