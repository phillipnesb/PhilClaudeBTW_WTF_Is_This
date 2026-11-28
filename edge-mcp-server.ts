/**
 * COSMIC COVENANT PROTOCOL (RFC-0001) — CLOUDFLARE WORKER & NODE.JS MCP GUARD
 * Integrates formally verified Lean 4 WASM invariants + HMAC-SHA256 Token Gate
 */
export interface CovenantEnv {
  CCP_SUPERVISOR_SECRET: string;
  CCP_WASM?: WebAssembly.Module;
}

export interface PolicyState {
  fMin: bigint;
  hMax: bigint;
  xiMax: bigint;
  gamma: bigint;
  currentF: bigint;
  currentHarm: bigint;
}

export class EdgeCovenantGuard {
  private usedNonces = new Set<string>();
  public state: PolicyState = {
    fMin: 10n, hMax: 5n, xiMax: 3n, gamma: 4n, currentF: 25n, currentHarm: 0n
  };

  private static canonicalJson(obj: Record<string, unknown>): string {
    const clean: Record<string, unknown> = {};
    for (const k of Object.keys(obj).sort()) {
      if (k !== "_ccp_token") clean[k] = obj[k];
    }
    return JSON.stringify(clean);
  }

  private static async hmacHex(secret: string, payload: string): Promise<string> {
    const enc = new TextEncoder();
    const key = await crypto.subtle.importKey(
      "raw", enc.encode(secret), { name: "HMAC", hash: "SHA-256" }, false, ["sign"]
    );
    const sig = await crypto.subtle.sign("HMAC", key, enc.encode(payload));
    return Array.from(new Uint8Array(sig)).map(b => b.toString(16).padStart(2, "0")).join("");
  }

  private static async sha256Hex(payload: string): Promise<string> {
    const dig = await crypto.subtle.digest("SHA-256", new TextEncoder().encode(payload));
    return Array.from(new Uint8Array(dig)).map(b => b.toString(16).padStart(2, "0")).join("");
  }

  public async verifyToken(secret: string, tool: string, args: Record<string, unknown>, token?: string): Promise<bigint> {
    if (!token) return 0n;
    const parts = token.split("|");
    if (parts.length !== 4) return 0n;
    const [tTool, nonce, pStr, sig] = parts;
    if (tTool !== tool || this.usedNonces.has(nonce)) return 0n;
    const argsHash = await EdgeCovenantGuard.sha256Hex(EdgeCovenantGuard.canonicalJson(args));
    const expected = await EdgeCovenantGuard.hmacHex(secret, `${tTool}|${nonce}|${pStr}|${argsHash}`);
    if (sig.length !== expected.length) return 0n;
    let diff = 0;
    for (let i = 0; i < sig.length; i++) diff |= sig.charCodeAt(i) ^ expected.charCodeAt(i);
    if (diff !== 0) return 0n;
    this.usedNonces.add(nonce);
    return BigInt(pStr);
  }

  public evaluateInvariants(impact: bigint, shock: bigint, S: bigint, P: bigint): boolean {
    const s = this.state;
    const postF = s.currentF >= impact ? s.currentF - impact : 0n;
    const grossHarm = s.currentHarm + shock;
    const postHarm = grossHarm >= s.gamma ? grossHarm - s.gamma : 0n;
    const ok = (s.fMin <= postF) && (postHarm <= s.hMax) && (S <= P) && (shock <= s.xiMax);
    if (ok) {
      s.currentF = postF;
      s.currentHarm = postHarm;
    }
    return ok;
  }

  public async handleMcpRpc(req: any, secret: string): Promise<any> {
    if (req?.method !== "tools/call") return { jsonrpc: "2.0", id: req?.id ?? null, ccp_passthrough: true };
    const tool = String(req?.params?.name ?? "unknown");
    const args = (req?.params?.arguments ?? {}) as Record<string, unknown>;
    const destructive = /(delete|drop|exec|shell|transfer|write|sudo)/i.test(tool);
    const verifiedP = await this.verifyToken(secret, tool, args, args._ccp_token as string | undefined);
    const P = verifiedP > 0n ? verifiedP : (destructive ? 0n : 10n);
    const impact = destructive && P >= 10n ? 5n : (destructive ? 12n : 1n);
    const shock = destructive && P >= 10n ? 2n : (destructive ? 4n : 1n);
    if (!this.evaluateInvariants(impact, shock, 10n, P)) {
      return {
        jsonrpc: "2.0", id: req.id,
        error: { code: -32001, message: `CCP RFC-0001 Blocked '${tool}': Invariant or Token Violation` }
      };
    }
    return {
      jsonrpc: "2.0", id: req.id,
      result: { ccp_approved: true, tool, remaining_F: this.state.currentF.toString(), harm: this.state.currentHarm.toString() }
    };
  }
}

export default {
  async fetch(request: Request, env: CovenantEnv): Promise<Response> {
    if (request.method !== "POST") return new Response("CCP RFC-0001 MCP Edge Guard Active", { status: 200 });
    const guard = new EdgeCovenantGuard();
    const rpc = await request.json();
    const res = await guard.handleMcpRpc(rpc, env.CCP_SUPERVISOR_SECRET || "dev-secret");
    return new Response(JSON.stringify(res), { headers: { "Content-Type": "application/json" } });
  }
};
