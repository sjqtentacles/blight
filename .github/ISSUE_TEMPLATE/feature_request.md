---
name: Feature request
about: Suggest a capability for Blight
title: ""
labels: enhancement
assignees: ""
---

## Problem / motivation

What are you trying to do that Blight does not support today?

## Proposed solution

What would you like to see? If it is a language feature, sketch the surface syntax and how it
elaborates.

## Trust boundary

Where would this live? Recall that only `blight-kernel` is trusted — most features should be
*tower* code (in `blight-elab`, the prelude, etc.) that bottoms out in the existing kernel rules.
If this genuinely needs a kernel change, explain why it cannot be built on top.

## Alternatives considered

Other designs you thought about, and why you prefer the proposal.
