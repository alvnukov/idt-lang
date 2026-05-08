from __future__ import annotations

import json
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import TextIO

from theory_verifier.ai_theory_graph import JsonObject, V8GraphQueryError
from theory_verifier.idt_rag import (
    IdtRagError,
    IdtRagIndex,
    audit_result_text,
    check_evidence_text,
    graph_diff_text,
    guarded_edit_text,
    missing_artifacts_text,
    optional_bool_arg,
    optional_int_arg,
    optional_string_arg,
    rag_result_text,
    research_context_text,
    require_string_arg,
)


JsonRpcId = str | int | None


@dataclass(frozen=True)
class JsonRpcRequest:
    request_id: JsonRpcId
    method: str
    params: Mapping[str, object]


class IdtMcpError(ValueError):
    pass


@dataclass(frozen=True)
class IdtMcpServer:
    index: IdtRagIndex
    auto_refresh: bool = True

    def handle_payload(self, payload: Mapping[str, object]) -> JsonObject | None:
        request = parse_json_rpc_request(payload)
        if request.method == "notifications/initialized":
            return None
        try:
            result = self.dispatch(request.method, request.params)
            return json_rpc_result(request.request_id, result)
        except (IdtMcpError, IdtRagError, V8GraphQueryError) as error:
            return json_rpc_error(request.request_id, -32602, str(error))

    def dispatch(self, method: str, params: Mapping[str, object]) -> JsonObject:
        if method == "initialize":
            return {
                "protocolVersion": "2024-11-05",
                "serverInfo": {
                    "name": "idt-v8-dev-mcp",
                    "version": "0.1.0",
                },
                "capabilities": {
                    "tools": {},
                    "resources": {},
                },
            }
        if method == "tools/list":
            return {"tools": mcp_tools()}
        if method == "tools/call":
            return self.call_tool(params)
        raise IdtMcpError(f"unsupported MCP method {method!r}")

    def call_tool(self, params: Mapping[str, object]) -> JsonObject:
        index = self.current_index()
        tool_name = require_string_arg(params, "name")
        arguments = optional_object(params.get("arguments", {}), "arguments")
        if tool_name == "idt_graph_summary":
            return mcp_text_result(index.summary())
        if tool_name == "idt_graph_search":
            query = require_string_arg(arguments, "query")
            kind = optional_string_arg(arguments, "kind")
            status = optional_string_arg(arguments, "status")
            limit = optional_int_arg(arguments, "limit", 20)
            return mcp_text_result(index.search_graph(query, kind, status, limit))
        if tool_name == "idt_graph_show":
            query = require_string_arg(arguments, "query")
            return mcp_text_result(index.show(query))
        if tool_name == "idt_graph_neighbors":
            query = require_string_arg(arguments, "query")
            depth = optional_int_arg(arguments, "depth", 1)
            return mcp_text_result(index.neighborhood(query, depth))
        if tool_name == "idt_graph_sources":
            query = require_string_arg(arguments, "query")
            depth = optional_int_arg(arguments, "depth", 1)
            return mcp_text_result(index.sources(query, depth))
        if tool_name == "idt_rag_retrieve":
            query = require_string_arg(arguments, "query")
            limit = optional_int_arg(arguments, "limit", 8)
            max_lines = optional_int_arg(arguments, "max_lines_per_source", 8)
            result = index.retrieve(query, limit, max_lines)
            return mcp_text_result(result, text=rag_result_text(result))
        if tool_name == "idt_research_context":
            query = require_string_arg(arguments, "query")
            depth = optional_int_arg(arguments, "depth", 1)
            limit = optional_int_arg(arguments, "limit", 8)
            result = index.research_context(query, depth, limit)
            return mcp_text_result(result, text=research_context_text(result))
        if tool_name == "idt_claim_audit":
            result = index.claim_audit()
            return mcp_text_result(result, text=audit_result_text(result))
        if tool_name == "idt_missing_proof_artifacts":
            limit = optional_int_arg(arguments, "limit", 50)
            result = index.missing_proof_artifacts(limit)
            return mcp_text_result(result, text=missing_artifacts_text(result))
        if tool_name == "idt_graph_diff":
            base_graph = require_string_arg(arguments, "base_graph")
            limit = optional_int_arg(arguments, "limit", 40)
            result = index.graph_diff(Path(base_graph), limit)
            return mcp_text_result(result, text=graph_diff_text(result))
        if tool_name == "idt_lean_build_target":
            target = require_string_arg(arguments, "target")
            timeout_seconds = optional_int_arg(arguments, "timeout_seconds", 60)
            result = index.lean_build_target(target, timeout_seconds)
            return mcp_text_result(result, text=check_evidence_text(result))
        if tool_name == "idt_run_check":
            name = require_string_arg(arguments, "name")
            result = index.run_check(name)
            return mcp_text_result(result, text=check_evidence_text(result))
        if tool_name == "idt_guarded_replace":
            file_path = require_string_arg(arguments, "file_path")
            expected_sha16 = require_string_arg(arguments, "expected_sha16")
            old_text = require_string_arg(arguments, "old_text")
            new_text = require_string_arg(arguments, "new_text")
            dry_run = optional_bool_arg(arguments, "dry_run", True)
            result = index.guarded_replace(
                Path(file_path),
                expected_sha16,
                old_text,
                new_text,
                dry_run,
            )
            return mcp_text_result(result, text=guarded_edit_text(result))
        raise IdtMcpError(f"unknown IDT MCP tool {tool_name!r}")

    def current_index(self) -> IdtRagIndex:
        if not self.auto_refresh:
            return self.index
        return self.index.refresh()


def mcp_tools() -> list[JsonObject]:
    return [
        tool_schema(
            "idt_graph_summary",
            "Summarize the compact IDT v8 AI theory graph.",
            {},
        ),
        tool_schema(
            "idt_graph_search",
            "Search IDT v8 graph node ids, labels, statuses, kinds, and sources.",
            {
                "query": {"type": "string"},
                "kind": {"type": "string"},
                "status": {"type": "string"},
                "limit": {"type": "integer"},
            },
            required=("query",),
        ),
        tool_schema(
            "idt_graph_show",
            "Show one graph node plus incoming and outgoing edges.",
            {"query": {"type": "string"}},
            required=("query",),
        ),
        tool_schema(
            "idt_graph_neighbors",
            "Show a local graph neighborhood.",
            {"query": {"type": "string"}, "depth": {"type": "integer"}},
            required=("query",),
        ),
        tool_schema(
            "idt_graph_sources",
            "Show source pointers for a local graph neighborhood.",
            {"query": {"type": "string"}, "depth": {"type": "integer"}},
            required=("query",),
        ),
        tool_schema(
            "idt_rag_retrieve",
            "Retrieve compact source-grounded IDT development context. This is not proof authority.",
            {
                "query": {"type": "string"},
                "limit": {"type": "integer"},
                "max_lines_per_source": {"type": "integer"},
            },
            required=("query",),
        ),
        tool_schema(
            "idt_research_context",
            "Return compact graph context, audit status, neighborhoods, and source pointers for an IDT research query.",
            {
                "query": {"type": "string"},
                "depth": {"type": "integer"},
                "limit": {"type": "integer"},
            },
            required=("query",),
        ),
        tool_schema(
            "idt_claim_audit",
            "Audit graph claim boundaries. Flags formal_proof residuals without Lean-grounded artifacts.",
            {},
        ),
        tool_schema(
            "idt_missing_proof_artifacts",
            "List proof-relevant theorem cards and QM obligations that are not formal_proof Lean artifacts.",
            {"limit": {"type": "integer"}},
        ),
        tool_schema(
            "idt_graph_diff",
            "Compare the live v8 graph against another repo-local graph file.",
            {"base_graph": {"type": "string"}, "limit": {"type": "integer"}},
            required=("base_graph",),
        ),
        tool_schema(
            "idt_lean_build_target",
            "Run lake build for a safe Lean target and return a compact evidence pack.",
            {"target": {"type": "string"}, "timeout_seconds": {"type": "integer"}},
            required=("target",),
        ),
        tool_schema(
            "idt_run_check",
            "Run an allowlisted IDT quality check and return a compact evidence pack.",
            {"name": {"type": "string"}},
            required=("name",),
        ),
        tool_schema(
            "idt_guarded_replace",
            "Guarded single-file text replacement with hash check, lock, atomic write, and forbidden claim/status scan.",
            {
                "file_path": {"type": "string"},
                "expected_sha16": {"type": "string"},
                "old_text": {"type": "string"},
                "new_text": {"type": "string"},
                "dry_run": {"type": "boolean"},
            },
            required=("file_path", "expected_sha16", "old_text", "new_text"),
        ),
    ]


def tool_schema(
    name: str,
    description: str,
    properties: Mapping[str, object],
    required: Sequence[str] = (),
) -> JsonObject:
    return {
        "name": name,
        "description": description,
        "inputSchema": {
            "type": "object",
            "properties": dict(properties),
            "required": list(required),
            "additionalProperties": False,
        },
    }


def mcp_text_result(payload: Mapping[str, object], text: str | None = None) -> JsonObject:
    rendered = text if text is not None else json.dumps(payload, ensure_ascii=False, sort_keys=True)
    return {
        "content": [
            {
                "type": "text",
                "text": rendered,
            }
        ],
        "structuredContent": dict(payload),
    }


def parse_json_rpc_request(payload: Mapping[str, object]) -> JsonRpcRequest:
    jsonrpc = payload.get("jsonrpc")
    if jsonrpc != "2.0":
        raise IdtMcpError("jsonrpc must be '2.0'")
    method = payload.get("method")
    if not isinstance(method, str) or not method:
        raise IdtMcpError("method must be a non-empty string")
    request_id = parse_request_id(payload.get("id"))
    params = optional_object(payload.get("params", {}), "params")
    return JsonRpcRequest(request_id, method, params)


def parse_request_id(value: object) -> JsonRpcId:
    if value is None or isinstance(value, str):
        return value
    if isinstance(value, int) and not isinstance(value, bool):
        return value
    raise IdtMcpError("id must be string, integer, or null")


def optional_object(value: object, field: str) -> Mapping[str, object]:
    if not isinstance(value, dict):
        raise IdtMcpError(f"{field} must be an object")
    output: dict[str, object] = {}
    for key, item in value.items():
        if not isinstance(key, str):
            raise IdtMcpError(f"{field} keys must be strings")
        output[key] = item
    return output


def json_rpc_result(request_id: JsonRpcId, result: Mapping[str, object]) -> JsonObject:
    return {
        "jsonrpc": "2.0",
        "id": request_id,
        "result": dict(result),
    }


def json_rpc_error(request_id: JsonRpcId, code: int, message: str) -> JsonObject:
    return {
        "jsonrpc": "2.0",
        "id": request_id,
        "error": {
            "code": code,
            "message": message,
        },
    }


def serve(server: IdtMcpServer, stdin: TextIO, stdout: TextIO) -> int:
    for raw_line in stdin:
        line = raw_line.strip()
        if not line:
            continue
        response = handle_line(server, line)
        if response is not None:
            stdout.write(json.dumps(response, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
            stdout.write("\n")
            stdout.flush()
    return 0


def handle_line(server: IdtMcpServer, line: str) -> JsonObject | None:
    try:
        raw = json.loads(line)
    except json.JSONDecodeError as error:
        return json_rpc_error(None, -32700, f"invalid JSON: {error}")
    if not isinstance(raw, dict):
        return json_rpc_error(None, -32600, "JSON-RPC payload must be an object")
    try:
        return server.handle_payload(raw)
    except IdtMcpError as error:
        return json_rpc_error(None, -32600, str(error))


def load_server(repo_root: Path, graph_path: Path) -> IdtMcpServer:
    return IdtMcpServer(IdtRagIndex.load(repo_root, graph_path, check_source_hashes=True, auto_refresh=True))
