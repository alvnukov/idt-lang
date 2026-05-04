namespace IDT

def currentFormalClaimRefs : List String :=
  [
    "finite_gates.idt_core_bounded_arity_frontier_demo.bounded_correlation_arity_bound.status",
    "finite_gates.idt_core_bounded_arity_frontier_demo.context_product_arity_bound.status",
    "finite_gates.idt_core_bounded_arity_frontier_demo.recoverable_filter_arity_bound.status",
    "finite_gates.idt_core_bounded_arity_frontier_demo.state_effect_witness_arity_bound.status",
    "finite_gates.idt_core_finite_signature_frontier_demo.finite_claim_role_vocabulary.status",
    "finite_gates.idt_core_finite_signature_frontier_demo.finite_gate_type_registry.status",
    "finite_gates.idt_core_finite_signature_frontier_demo.finite_primitive_sort_vocabulary.status",
    "finite_gates.idt_core_finite_signature_frontier_demo.finite_route_family_registry.status",
    "finite_gates.idt_core_gate_type_registry_audit_demo.idt_core_gate_type_registry_audit_demo.expected_component_status",
    "finite_gates.idt_core_no_new_primitive_effects_frontier_demo.finite_effect_registry.status",
    "finite_gates.idt_core_no_new_primitive_effects_frontier_demo.joint_only_invariant_rejection.status",
    "finite_gates.idt_core_no_new_primitive_effects_frontier_demo.route_closure_effect_audit.status",
    "finite_gates.idt_core_route_generator_basis_frontier_demo.bounded_correlation_generators.status",
    "finite_gates.idt_core_route_generator_basis_frontier_demo.context_product_generators.status",
    "finite_gates.idt_core_route_generator_basis_frontier_demo.recoverable_filter_generators.status",
    "finite_gates.idt_core_route_generator_basis_frontier_demo.state_effect_generators.status",
    "finite_gates.idt_core_route_grammar_audit_demo.bounded_correlation_arity_bound.expected_component_status",
    "finite_gates.idt_core_route_grammar_audit_demo.bounded_correlation_generators.expected_component_status",
    "finite_gates.idt_core_route_grammar_audit_demo.context_product_arity_bound.expected_component_status",
    "finite_gates.idt_core_route_grammar_audit_demo.context_product_generators.expected_component_status",
    "finite_gates.idt_core_route_grammar_audit_demo.finite_effect_registry.expected_component_status",
    "finite_gates.idt_core_route_grammar_audit_demo.recoverable_filter_arity_bound.expected_component_status",
    "finite_gates.idt_core_route_grammar_audit_demo.recoverable_filter_generators.expected_component_status",
    "finite_gates.idt_core_route_grammar_audit_demo.route_closure_effect_audit.expected_component_status",
    "finite_gates.idt_core_route_grammar_audit_demo.state_effect_generators.expected_component_status",
    "finite_gates.idt_core_route_grammar_audit_demo.state_effect_witness_arity_bound.expected_component_status",
    "finite_gates.idt_core_semantic_no_new_effects_audit_demo.joint_only_invariant_rejection.status",
    "finite_gates.idt_core_signature_registry_audit_demo.finite_claim_role_vocabulary.expected_component_status",
    "finite_gates.idt_core_signature_registry_audit_demo.finite_primitive_sort_vocabulary.expected_component_status",
    "finite_gates.idt_core_signature_registry_audit_demo.finite_route_family_registry.expected_component_status",
    "finite_gates.uniform_witness_bound_assumption_frontier_demo.bounded_context_arity.status",
    "finite_gates.uniform_witness_bound_assumption_frontier_demo.finite_context_signature.status",
    "finite_gates.uniform_witness_bound_assumption_frontier_demo.finite_route_generator_basis.status"
  ]

theorem current_formal_claim_ledger_count :
    currentFormalClaimRefs.length = 33 := by
  native_decide

theorem current_formal_claim_ledger_nonempty :
    currentFormalClaimRefs ≠ [] := by
  native_decide

theorem current_formal_claim_ledger_nodup :
    currentFormalClaimRefs.Nodup := by
  native_decide

end IDT
