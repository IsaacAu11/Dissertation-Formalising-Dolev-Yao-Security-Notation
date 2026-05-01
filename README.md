# Proving Security Theorems in Lean 4

A dissertation project formalising cryptographic protocol security in Lean 4. The library models protocol participants, messages, and cryptographic operations, then uses an inductive knowledge predicate. Inspired by the Dolev-Yao attacker model and built to state and prove what each principal (including an adversary) can or cannot learn from a protocol transcript.

The primary test case is a simplified TLS handshake, with a machine-checked proof that a passive adversary cannot derive the pre-master secret without the server's private key.

## Project Structure

```
SecurityNotation/
├── Basic/
│   ├── Syntax/
│   │   ├── Principal.lean     -- Principal, Role
│   │   ├── Keys.lean          -- Key, KeyId, KeyType
│   │   ├── Nonces.lean        -- Nonce
│   │   ├── Messages.lean      -- BaseMessage, MessageEnc1, MessageEnc2
│   │   └── Events.lean        -- Event (send/receive), Trace
│   └── Utils/
│       └── Notation.lean      -- NON, KEY, AGT, MSG, ⟨⟩, {||}
├── Logic/
│   └── Logic.lean             -- KnowsFromTrace, Knows
└── Testing/
    └── tlsHandshake.lean      -- TLS trace definition + security theorems
```

## TLS Handshake Example

`Testing/tlsHandshake.lean` models a four-step simplified TLS handshake between Alice and the Server, observed by Eve (adversary):

1. Alice → Server: `NON aliceNonce`
2. Server → Alice: `⟨ serverNonce, serverPublicKey ⟩`
3. Alice → Server: `{| preMasterSecret |} serverPublicKey`
4. Server → Alice: `{| aliceNonce |} sessionKey`

## AI declaration

AI (Claude, Anthropic) was used to assist with the code and proof development, specifically tlsHandshake 'EveKnowsNoPrivateKey' and helper lemmas.

## Dependencies

- [Std4](https://github.com/leanprover/std4) `v4.26.0`
- [Batteries](https://github.com/leanprover-community/batteries) `v4.26.0`

Built with Lean 4 / Lake.
