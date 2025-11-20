#include "TunnelReduction.h"
#include "Z3Tools.h"
#include "stdio.h"

/**
 * @brief Creates the variable "x_{node,pos,stack_height}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param node A node.
 * @param pos The path position.
 * @param stack_height The highest cell occupied of the stack at that position.
 * @return Z3_ast
 */
Z3_ast tn_path_variable(Z3_context ctx, int node, int pos, int stack_height)
{
    char name[60];
    snprintf(name, 60, "node %d,pos %d, height %d", node, pos, stack_height);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Creates the variable "y_{pos,height,4}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param pos The path position.
 * @param height The height of the cell described.
 * @return Z3_ast
 */
Z3_ast tn_4_variable(Z3_context ctx, int pos, int height)
{
    char name[60];
    snprintf(name, 60, "4 at height %d on pos %d", height, pos);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Creates the variable "y_{pos,height,6}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param pos The path position.
 * @param height The height of the cell described.
 * @return Z3_ast
 */
Z3_ast tn_6_variable(Z3_context ctx, int pos, int height)
{
    char name[60];
    snprintf(name, 60, "6 at height %d on pos %d", height, pos);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Wrapper to have the correct size of the array representing the stack (correct cells of the stack will be from 0 to (get_stack_size(length)-1)).
 *
 * @param length The length of the sought path.
 * @return int
 */
int get_stack_size(int length)
{
    return length / 2 + 1;
}

/** 
 * @brief Créer la formule φ1
 */

Z3_ast create_phi_1(Z3_context ctx, const TunnelNetwork network, int length)
{
   //Récupérer le nombre de noeuds dans le réseau
   int num_nodes = tn_get_num_nodes(network);

   //Calculer la hauteur maximale de la pile
   int stack_size = get_stack_size(length);

   // Créer un tableau pour stocker les formules unique de chaque position
   Z3_ast phi_1_conjuncts[length + 1]; // Car on a les positions de 0 à length

   for (int pos = 0; pos <= length; pos++)
  {
    // Calculer le nombre de vars pour cette position
    int num_variables = num_nodes * stack_size;
    Z3_ast variables[num_variables]; 

    int var_index = 0;

    // for chaque noeud 
    for (int node = 0; node < num_nodes; node ++)
   {
     // Pour chaque hauteur possible
     for (int height = 0; height < stack_size; height++)
    {
        // Créer la variable x{node, pos, height}
        variables[var_index] = tn_path_variable(ctx, node, pos, height);
        var_index++;  
    } 
   } 
   //uniqueFormula = exactement une des vars du tab est vraie
    phi_1_conjuncts[pos] = uniqueFormula(ctx, variables, num_variables); 
  } 
   //Faire la conjonction de toutes des formules Unique
   return Z3_mk_and(ctx, length + 1, phi_1_conjuncts);
}

/**
 * Créer φ2 exprimant les conditions initiales et fianles
*/

Z3_ast create_phi_2(Z3_context ctx, const TunnelNetwork network, int length)
{
    // Récupérer le noeud source
    int source = tn_get_initial(network);

    // Récupérer le noeud destination 
    int destination = tn_get_final(network);

    // x{source,0,0} 
    Z3_ast x_initial = tn_path_variable(ctx, source, 0, 0);
    
    // y{0,0,4}
    Z3_ast y_initial = tn_4_variable(ctx, 0, 0);
    
    Z3_ast phi_2_initial_parts[2] = {x_initial, y_initial};
    Z3_ast phi_2_initial = Z3_mk_and(ctx, 2, phi_2_initial_parts);
    
    // x{dest, length,0}
    Z3_ast x_final = tn_path_variable(ctx, destination, length, 0);
    
    // y{length,0,4}
    Z3_ast y_final = tn_4_variable(ctx, length, 0); 

    Z3_ast phi_2_final_parts[2] = {x_final, y_final};
    Z3_ast phi_2_final = Z3_mk_and(ctx, 2, phi_2_final_parts);  
    
    Z3_ast phi_2_parts[2] = {phi_2_initial, phi_2_final};
    return Z3_mk_and(ctx, 2, phi_2_parts);   
}

/**
 * Pour chaque transmission, la hauteur reste identique
 */

Z3_ast create_phi_3_trans(Z3_context ctx, const TunnelNetwork network, int length)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(length);

    // Tableau pour stocker toutes les implications
    int max_implications = length * num_nodes * stack_size * 2;
    Z3_ast implications[max_implications];
    int impl_count = 0;
    
    // Pour chaque transition de i à i+1
    for(int pos = 0; pos < length; pos ++)
   {
    // Pour chaque noeud
        for (int node = 0; node < num_nodes; node++)
        {
            //Pour chaque hauteur
            for (int height = 0; height < stack_size; height++)
            {
                //Pour chaque protocole
                for (int protocol = 4; protocol <=6; protocol +=2)
               {
                    // Vérifier si le noeud peut faire une transmission de ce protocole
                    stack_action action = (protocol == 4) ? transmit_4 : transmit_6;

                    if(!tn_node_has_action(network, node, action))
                        continue; // Ce noeud ne peut pas faire cette action

                    //x{node,pos,height} ∧ y{pos, height, protocol}
                    Z3_ast premise_parts[2];
                    premise_parts[0] = tn_path_variable(ctx, node, pos, height);
                    premise_parts[1] = (protocol == 4) ?
                                        tn_4_variable(ctx, pos, height):
                                        tn_6_variable(ctx, pos, height);
                    Z3_ast premise = Z3_mk_and(ctx, 2, premise_parts); 
                        
                    // On cherche tous les voisins de node
                    Z3_ast neighbors[num_nodes]; // Au max num_nodes voisins
                    int neighbor_count = 0;
                        
                    for(int neighbor = 0; neighbor < num_nodes; neighbor++)
                    {
                        // Vérifier s'il existe une arete uv
                        if(tn_is_edge(network, node, neighbor))
                        {
                            // x{neighbor,pos+1,height}(même hauteur)
                            neighbors[neighbor_count] = tn_path_variable(ctx, neighbor, pos + 1, height);
                            neighbor_count++;  
                        } 
                    } 

                    // Si aucun voisin, l'implication est vacuement vraie
                    if (neighbor_count == 0)
                        continue;
                         
                    Z3_ast conclusion = Z3_mk_or(ctx, neighbor_count, neighbors);

                    // premise => conclusion
                    implications[impl_count] = Z3_mk_implies(ctx, premise, conclusion);
                    impl_count++; 
                } 
            }
            
        } 
   } 

   // Si aucune implication, retourner vrai
   if(impl_count == 0)
        return Z3_mk_true(ctx);

   // Faire la conjonction de toutes les implications
   return Z3_mk_and(ctx, impl_count, implications);     
}

/**
 * Pour chaque encapsulation, la hauteur augmente de 1.
 */

Z3_ast create_phi_3_push(Z3_context ctx, const TunnelNetwork network, int length)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(length);

    int max_implications = length * num_nodes * stack_size * 4; // 4 combinaisons a,b
    Z3_ast implications[max_implications];
    int impl_count = 0;
    
    // Pour chaque transition
    for (int pos = 0; pos < length; pos++)
   {
        // Pour chaque noeud
        for (int node = 0; node < num_nodes; node++)
       {
            // Pour vhaque hauteur 
            for (int height = 0; height < stack_size - 1; height ++)
            {
                // Pour chaque combinaison(a, b) de protocoles
                for(int protocol_a = 4; protocol_a <=6; protocol_a +=2)
                {
                    for (int protocol_b = 4; protocol_b <=6; protocol_b +=2)
                    {
                        // push correspondant
                        stack_action action;
                        if(protocol_a == 4 && protocol_b ==4) action = push_4_4;
                        else if (protocol_a == 4 && protocol_b == 6) action = push_4_6;
                        else if (protocol_a == 6 && protocol_b == 4) action = push_6_4;
                        else action = push_6_6;

                        if (!tn_node_has_action(network, node, action))
                            continue;

                        // Prémisse
                        Z3_ast premise_parts[2];
                        premise_parts[0] = tn_path_variable(ctx, node, pos, height);
                        premise_parts[1] = (protocol_a == 4)?
                                            tn_4_variable(ctx, pos, height):
                                            tn_6_variable(ctx, pos, height);
                        Z3_ast premise = Z3_mk_and(ctx, 2, premise_parts);
                    
                        // Conclusion
                        Z3_ast neighbors[num_nodes];
                        int neighbor_count = 0;
                    
                        for (int neighbor = 0; neighbor < num_nodes; neighbor++)
                        {
                            if(tn_is_edge(network, node, neighbor))
                            {
                                //x{neighbor, pos+1, height+1} ∧ y{pos+1, height+1, protocol_b}
                                Z3_ast neighbor_parts[2];
                                neighbor_parts[0] = tn_path_variable(ctx, neighbor, pos + 1, height + 1);
                                neighbor_parts[1] = (protocol_b == 4)?
                                                tn_4_variable(ctx, pos + 1, height + 1):
                                                tn_6_variable(ctx, pos + 1, height + 1);
                                neighbors[neighbor_count] = Z3_mk_and(ctx, 2, neighbor_parts);
                                neighbor_count++;
                            } 
                        } 
                        if (neighbor_count == 0)
                        continue;

                        Z3_ast conclusion = Z3_mk_or(ctx, neighbor_count, neighbors);
                   
                        // Implication
                         implications[impl_count] = Z3_mk_implies(ctx, premise, conclusion);
                        impl_count++; 
                    } 
                } 
            } 
        } 
    } 
    if (impl_count == 0)
        return Z3_mk_true(ctx);
    return Z3_mk_and(ctx, impl_count, implications);       
}

/**
 * Pour chaque désencapsulation, la hauteur diminue de 1.
 */

Z3_ast create_phi_3_pop(Z3_context ctx, const TunnelNetwork network, int length)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(length);

    int max_implications = length * num_nodes * stack_size * 4; // 4 combinaisons a,b
    Z3_ast implications[max_implications];
    int impl_count = 0;
    
    // Pour chaque transition
    for (int pos = 0; pos < length; pos++)
   {
        // Pour chaque noeud
        for (int node = 0; node < num_nodes; node++)
       {
            // Pour vhaque hauteur 
            for (int height = 1; height < stack_size; height ++)
            {
                // Pour chaque combinaison(a, b) de protocoles
                for(int protocol_a = 4; protocol_a <=6; protocol_a +=2)
                {
                    for (int protocol_b = 4; protocol_b <=6; protocol_b +=2)
                    {
                        // pop correspondant
                        stack_action action;
                        if(protocol_a == 4 && protocol_b ==4) action = pop_4_4;
                        else if (protocol_a == 4 && protocol_b == 6) action = pop_4_6;
                        else if (protocol_a == 6 && protocol_b == 4) action = pop_6_4;
                        else action = pop_6_6;

                        if (!tn_node_has_action(network, node, action))
                            continue;

                        // Prémisse
                        Z3_ast premise_parts[2];
                        premise_parts[0] = tn_path_variable(ctx, node, pos, height);
                        premise_parts[1] = (protocol_b == 4)?
                                            tn_4_variable(ctx, pos, height):
                                            tn_6_variable(ctx, pos, height);
                        premise_parts[2] = (protocol_a == 4)?
                                            tn_4_variable(ctx, pos, height - 1):
                                            tn_6_variable(ctx, pos, height - 1);
                        Z3_ast premise = Z3_mk_and(ctx, 3, premise_parts);
                    
                        // Conclusion
                        Z3_ast neighbors[num_nodes];
                        int neighbor_count = 0;
                    
                        for (int neighbor = 0; neighbor < num_nodes; neighbor++)
                        {
                            if(tn_is_edge(network, node, neighbor))
                            {
                                neighbors[neighbor_count] = tn_path_variable(ctx, neighbor, pos + 1, height -1);
                                neighbor_count++;
                            } 
                        } 
                        if (neighbor_count == 0)
                        continue;

                        Z3_ast conclusion = Z3_mk_or(ctx, neighbor_count, neighbors);
                   
                        // Implication
                        implications[impl_count] = Z3_mk_implies(ctx, premise, conclusion);
                        impl_count++; 
                    } 
                } 
            } 
        } 
    } 
    if (impl_count == 0)
        return Z3_mk_true(ctx);
    return Z3_mk_and(ctx, impl_count, implications);    
}

Z3_ast create_phi_3(Z3_context ctx, const TunnelNetwork network, int length)
{
    Z3_ast phi_3_trans = create_phi_3_trans(ctx, network, length);
    Z3_ast phi_3_push = create_phi_3_push(ctx, network, length);
    Z3_ast phi_3_pop = create_phi_3_pop(ctx, network, length);
    Z3_ast phi_3_parts[3] ={phi_3_trans, phi_3_push, phi_3_pop};
    return Z3_mk_and(ctx, 3, phi_3_parts);  
}

/**
 * Créer la formule φ4 exprimant chaque cellule contient 4 ou 6 (exclusif)
 */

Z3_ast create_phi_4(Z3_context ctx, const TunnelNetwork network, int length)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(length);

    int max_implications = (length + 1) * stack_size;
    Z3_ast implications[max_implications];
    int impl_count = 0;
    
    // Pour chaque position
    for (int pos = 0; pos <= length; pos++)
   {
        // Pour chaque hauteur possible
        for (int height = 0; height < stack_size; height++)
       {
            // Prémisse
            Z3_ast premise_nodes[num_nodes];
            for (int node =0; node < num_nodes; node++)
            {
                premise_nodes[node] = tn_path_variable(ctx, node, pos, height);
            }  
            Z3_ast premise = Z3_mk_or(ctx, num_nodes, premise_nodes);

            // Conclusion
            Z3_ast cell_contraints[height + 1];
            for(int cell = 0; cell <= height; cell++)
            {
                // var pour cette cell
                Z3_ast y_4 = tn_4_variable(ctx, pos, cell);
                Z3_ast y_6 = tn_6_variable(ctx, pos, cell);

                // y{pos,cell,4} ∧ ¬y{pos,cell,6}  (contient 4 exclusif)
                Z3_ast contains_4_parts[2];
                contains_4_parts[0] = y_4;
                contains_4_parts[1] = Z3_mk_not(ctx, y_6);
                Z3_ast contains_4 = Z3_mk_and(ctx, 2, contains_4_parts);

                // ¬y{pos,cell,4} ∧ y{pos,cell,6}  (contient 6 exclusif)
                Z3_ast contains_6_parts[2];
                contains_6_parts[0] = Z3_mk_not(ctx, y_4);
                contains_6_parts[1] = y_6;
                Z3_ast contains_6 = Z3_mk_and(ctx, 2, contains_6_parts);
                
                // (contient 4 exclusif) ∨ (contient 6 exclusif)
                Z3_ast xor_parts[2] = {contains_4, contains_6};
                cell_contraints[cell] = Z3_mk_or(ctx, 2, xor_parts);

            }  
            // ∧ de toutes les contraintes sur les cellules
            Z3_ast conclusion = Z3_mk_and(ctx, height + 1, cell_contraints);
            // =>
            implications[impl_count] = Z3_mk_implies(ctx, premise, conclusion);
            impl_count++; 
       } 
   } 
   // ∧ de toutes les implications
   return Z3_mk_and(ctx, impl_count, implications);
}

/**
 * Vérifie que le sommet de pile corrspond à l'opération de transmission
 */
Z3_ast create_phi_5_trans(Z3_context ctx, const TunnelNetwork network, int length)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(length);

    int max_implications = (length + 1) * num_nodes * stack_size * 2;
    Z3_ast implications[max_implications]; 
    int impl_count = 0;

    //Pour chaque position
    for (int pos = 0; pos <= length; pos++)
   {
        // Pour chaque noeud
        for(int node = 0; node < num_nodes; node++)
       {
            // pour chaque hauteur
            for (int height =0; height < stack_size; height++)
           {
                // Pour chaque protocole (4 et 6)
                for (int protocol = 4; protocol <= 6; protocol +=2)
               {
                    stack_action action = (protocol == 4)? transmit_4: transmit_6;

                    if(!tn_node_has_action(network, node, action))
                        continue;
                    
                    // Prémisse
                    Z3_ast premise = tn_path_variable(ctx,node, pos, height) ;
                    
                    // Conclusion 
                    Z3_ast conclusion = (protocol == 4)?
                                        tn_4_variable(ctx, pos, height):
                                        tn_6_variable(ctx, pos, height);
                     
                    // Implication
                    implications[impl_count] = Z3_mk_implies(ctx, premise, conclusion);
                    impl_count++;                 
               } 
           } 
       } 
   } 
   if (impl_count == 0)
        return Z3_mk_true(ctx);
   return Z3_mk_and(ctx, impl_count, implications); 
}

/**
 * Vérifie que le sommet actuel correspond au protocole à encaplsuler
 */

Z3_ast create_phi_5_push(Z3_context ctx, const TunnelNetwork network, int length)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(length);

    int max_implications = (length + 1) * num_nodes * stack_size * 4;
    Z3_ast implications[max_implications]; 
    int impl_count = 0;

    //Pour chaque position
    for (int pos = 0; pos <= length; pos++)
   {
        // Pour chaque noeud
        for(int node = 0; node < num_nodes; node++)
       {
            // pour chaque hauteur
            for (int height =0; height < stack_size; height++)
           {
                // Pour chaque combinaison (a,b)
                for (int protocol_a = 4; protocol_a <= 6; protocol_a +=2)
               {
                    for (int protocol_b = 4; protocol_b <=6; protocol_b +=2)
                    {
                        // push correspondant
                        stack_action action;
                        if(protocol_a == 4 && protocol_b ==4) action = push_4_4;
                        else if (protocol_a == 4 && protocol_b == 6) action = push_4_6;
                        else if (protocol_a == 6 && protocol_b == 4) action = push_6_4;
                        else action = push_6_6;

                        if (!tn_node_has_action(network, node, action))
                            continue;       
                            
                        // Premisse 
                        Z3_ast premise = tn_path_variable(ctx, node, pos, height);
                        
                        // Conclusion
                        Z3_ast conclusion = (protocol_a == 4)?
                                            tn_4_variable(ctx, pos, height):
                                            tn_6_variable(ctx, pos, height);
                        
                        implications[impl_count] = Z3_mk_implies(ctx, premise, conclusion); 
                        impl_count++;                    
                    }   
                } 
            } 
        } 
    }     
   if (impl_count == 0)
        return Z3_mk_true(ctx);
   return Z3_mk_and(ctx, impl_count, implications); 
}

/**
 * Vérifie que le sommet actuel est b est juste dessous est a
 */

Z3_ast create_phi_5_pop(Z3_context ctx, const TunnelNetwork network, int length)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(length);

    int max_implications = (length + 1) * num_nodes * stack_size * 4;
    Z3_ast implications[max_implications]; 
    int impl_count = 0;

    //Pour chaque position
    for (int pos = 0; pos <= length; pos++)
   {
        // Pour chaque noeud
        for(int node = 0; node < num_nodes; node++)
       {
            // pour chaque hauteur
            for (int height = 1; height < stack_size; height++)
           {
                // Pour chaque combinaison (a,b)
                for (int protocol_a = 4; protocol_a <= 6; protocol_a +=2)
               {
                    for (int protocol_b = 4; protocol_b <=6; protocol_b +=2)
                    {
                        // pop correspondant
                        stack_action action;
                        if(protocol_a == 4 && protocol_b ==4) action = pop_4_4;
                        else if (protocol_a == 4 && protocol_b == 6) action = pop_4_6;
                        else if (protocol_a == 6 && protocol_b == 4) action = pop_6_4;
                        else action = pop_6_6;

                        if (!tn_node_has_action(network, node, action))
                            continue;       
                            
                        // Premisse 
                        Z3_ast premise = tn_path_variable(ctx, node, pos, height);
                        
                        // Conclusion
                        Z3_ast conclusion_parts[2];
                        conclusion_parts[0] = (protocol_b == 4)?
                                            tn_4_variable(ctx, pos, height):
                                            tn_6_variable(ctx, pos, height);
                        conclusion_parts[1] = (protocol_a == 4)?
                                            tn_4_variable(ctx, pos, height - 1):
                                            tn_6_variable(ctx, pos, height - 1);
                        Z3_ast conclusion = Z3_mk_and(ctx, 2, conclusion_parts);
                                     
                        // =>
                        implications[impl_count] = Z3_mk_implies(ctx, premise, conclusion); 
                        impl_count++;
                    }   
                } 
            } 
        } 
    }     
   if (impl_count == 0)
        return Z3_mk_true(ctx);
   return Z3_mk_and(ctx, impl_count, implications); 
}

Z3_ast create_phi_5(Z3_context ctx, const TunnelNetwork network, int length)
{
    Z3_ast phi_5_trans = create_phi_5_trans(ctx, network, length);
    Z3_ast phi_5_push = create_phi_5_push(ctx, network, length);
    Z3_ast phi_5_pop = create_phi_5_pop(ctx, network, length);

    Z3_ast phi_5_parts[3] ={phi_5_trans, phi_5_push, phi_5_pop};
    return Z3_mk_and(ctx, 3, phi_5_parts);  
}

/**
 * La préservation de la pile
 * Pour la transmission, la pile reste idéntique
 * Pour une encapsulation, les cellules 0 à h restent identiques, et on ajoute une couvelle cellule h+1
 * Pour chaque désencapsulation, les cellules de  à height - restent idéntiques
 */

Z3_ast create_phi_6_trans(Z3_context ctx, const TunnelNetwork network, int length)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(length);

    int max_implications = length * num_nodes * stack_size * 2;
    Z3_ast implications[max_implications];
    int impl_count = 0;

    //Pour chaque position
    for (int pos = 0; pos <= length; pos++)
   {
        // Pour chaque noeud
        for(int node = 0; node < num_nodes; node++)
       {
            // pour chaque hauteur
            for (int height =0; height < stack_size; height++)
           {
                // Pour chaque protocole (4 et 6)
                for (int protocol = 4; protocol <= 6; protocol +=2)
               {
                    stack_action action = (protocol == 4)? transmit_4: transmit_6;

                    if(!tn_node_has_action(network, node, action))
                        continue;
                    
                    // Prémisse
                    Z3_ast premise = tn_path_variable(ctx,node, pos, height) ;
                    
                    // Conclusion 
                    // Pour chaque cellule k de  à height, la cellule reste identique
                    Z3_ast cell_preservations[height + 1];
                    for (int cell = 0; cell <= height; cell++)
                   {
                    //y{pos,cell,4}<=>y{pos+1,cell,4}  
                    Z3_ast eq_4 = Z3_mk_eq(ctx, 
                                        tn_4_variable(ctx, pos, cell),
                                        tn_4_variable(ctx, pos + 1, cell));
                     
                    //y{pos,cell,6}<=>y{pos+1,cell,6}
                    Z3_ast eq_6 = Z3_mk_eq(ctx, 
                                        tn_6_variable(ctx, pos, cell),
                                        tn_6_variable(ctx, pos + 1, cell));

                    // Conjonction
                    Z3_ast preservation_parts[2] ={eq_4, eq_6};
                    cell_preservations[cell] = Z3_mk_and(ctx, 2, preservation_parts);    
                   } 
                   Z3_ast conclusion = Z3_mk_and(ctx, height + 1, cell_preservations);  
                    // Implication
                    implications[impl_count] = Z3_mk_implies(ctx, premise, conclusion);
                    impl_count++;                 
               } 
           } 
       } 
   } 
   if (impl_count == 0)
        return Z3_mk_true(ctx);
   return Z3_mk_and(ctx, impl_count, implications);     
}

Z3_ast create_phi_6_push(Z3_context ctx, const TunnelNetwork network, int length)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(length);

    int max_implications = length * num_nodes * stack_size * 2;
    Z3_ast implications[max_implications];
    int impl_count = 0;

    // Pour chaque transition
    for (int pos = 0; pos < length; pos++)
   {
        // Pour chaque noeud
        for (int node = 0; node < num_nodes; node++)
       {
            // Pour chaque hauteur 
            for (int height = 0; height < stack_size - 1; height ++)
            {
                // Pour chaque combinaison(a, b) de protocoles
                for(int protocol_a = 4; protocol_a <=6; protocol_a +=2)
                {
                    for (int protocol_b = 4; protocol_b <=6; protocol_b +=2)
                    {
                        // push correspondant
                        stack_action action;
                        if(protocol_a == 4 && protocol_b ==4) action = push_4_4;
                        else if (protocol_a == 4 && protocol_b == 6) action = push_4_6;
                        else if (protocol_a == 6 && protocol_b == 4) action = push_6_4;
                        else action = push_6_6;

                        if (!tn_node_has_action(network, node, action))
                            continue;

                        // Prémisse
                        Z3_ast premise = tn_path_variable(ctx,node, pos, height);
        
                        // Conclusion
                        Z3_ast cell_preservations[height + 1];
                        for (int cell = 0; cell <= height; cell++)
                        {
                        //y{pos,cell,4}<=>y{pos+1,cell,4}  
                        Z3_ast eq_4 = Z3_mk_eq(ctx, 
                                            tn_4_variable(ctx, pos, cell),
                                            tn_4_variable(ctx, pos + 1, cell));
                            
                        //y{pos,cell,6}<=>y{pos+1,cell,6}
                        Z3_ast eq_6 = Z3_mk_eq(ctx, 
                                            tn_6_variable(ctx, pos, cell),
                                            tn_6_variable(ctx, pos + 1, cell));

                        // Conjonction
                        Z3_ast preservation_parts[2] ={eq_4, eq_6};
                        cell_preservations[cell] = Z3_mk_and(ctx, 2, preservation_parts);    
                        } 
                        Z3_ast conclusion = Z3_mk_and(ctx, height + 1, cell_preservations);  
                            
                        
                        // Implication
                         implications[impl_count] = Z3_mk_implies(ctx, premise, conclusion);
                        impl_count++; 
                    } 
                } 
            } 
        } 
    } 
    if (impl_count == 0)
        return Z3_mk_true(ctx);
    return Z3_mk_and(ctx, impl_count, implications);       
}

Z3_ast create_phi_6_pop(Z3_context ctx, const TunnelNetwork network, int length)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(length);

    int max_implications = length * num_nodes * stack_size * 2;
    Z3_ast implications[max_implications];
    int impl_count = 0;

    // Pour chaque transition
    for (int pos = 0; pos < length; pos++)
   {
        // Pour chaque noeud
        for (int node = 0; node < num_nodes; node++)
       {
            // Pour chaque hauteur 
            for (int height = 1; height < stack_size; height ++)
            {
                // Pour chaque combinaison(a, b) de protocoles
                for(int protocol_a = 4; protocol_a <=6; protocol_a +=2)
                {
                    for (int protocol_b = 4; protocol_b <=6; protocol_b +=2)
                    {
                        // push correspondant
                        stack_action action;
                        if(protocol_a == 4 && protocol_b ==4) action = pop_4_4;
                        else if (protocol_a == 4 && protocol_b == 6) action = pop_4_6;
                        else if (protocol_a == 6 && protocol_b == 4) action = pop_6_4;
                        else action = pop_6_6;

                        if (!tn_node_has_action(network, node, action))
                            continue;

                        // Prémisse
                        Z3_ast premise = tn_path_variable(ctx,node, pos, height);
        
                        // Conclusion
                        // les cellules de 0 à height - 1 restent identiques et on retire la cellule height
                        if(height == 1)
                        {
                            //si height = 1, on verifie juste la cellule 0 
                            Z3_ast eq_4 = Z3_mk_eq(ctx, 
                                                tn_4_variable(ctx, pos, 0),
                                                tn_4_variable(ctx, pos + 1, 0));

                            Z3_ast eq_6 = Z3_mk_eq(ctx, 
                                                tn_6_variable(ctx, pos, 0),
                                                tn_6_variable(ctx, pos + 1, 0));

                            // Conjonction
                            Z3_ast preservation_parts[2] ={eq_4, eq_6};
                            Z3_ast conclusion = Z3_mk_and(ctx, 2, preservation_parts);    
                            implications[impl_count] = Z3_mk_implies(ctx, premise, conclusion);
                            impl_count++; 
                        } 
                        else 
                        {
                            Z3_ast cell_preservations[height];
                            for (int cell = 0; cell <= height; cell++)
                            {
                                Z3_ast eq_4 = Z3_mk_eq(ctx, 
                                                    tn_4_variable(ctx, pos, cell),
                                                    tn_4_variable(ctx, pos + 1, cell));

                                Z3_ast eq_6 = Z3_mk_eq(ctx, 
                                                    tn_6_variable(ctx, pos, cell),
                                                    tn_6_variable(ctx, pos + 1, cell));

                                // Conjonction
                                Z3_ast preservation_parts[2] ={eq_4, eq_6};
                                cell_preservations[cell] = Z3_mk_and(ctx, 2, preservation_parts);    
                            } 
                            Z3_ast conclusion = Z3_mk_and(ctx, height, cell_preservations);
                            implications[impl_count] = Z3_mk_implies(ctx, premise, conclusion);
                            impl_count ++; 
                        }        
                    } 
                } 
            } 
        } 
    } 
    if (impl_count == 0)
        return Z3_mk_true(ctx);
    return Z3_mk_and(ctx, impl_count, implications);       
}

Z3_ast create_phi_6(Z3_context ctx, const TunnelNetwork network, int length)
{
    Z3_ast phi_6_trans = create_phi_6_trans(ctx, network, length);
    Z3_ast phi_6_push = create_phi_6_push(ctx, network, length);
    Z3_ast phi_6_pop = create_phi_6_pop(ctx, network, length);

    Z3_ast phi_6_parts[3] ={phi_6_trans, phi_6_push, phi_6_pop};
    return Z3_mk_and(ctx, 3, phi_6_parts);  
}


Z3_ast tn_reduction(Z3_context ctx, const TunnelNetwork network, int length)
{
    Z3_ast phi_1 = create_phi_1(ctx, network, length);
    Z3_ast phi_2 = create_phi_2(ctx, network, length);
    Z3_ast phi_3 = create_phi_3(ctx, network, length);
    Z3_ast phi_4 = create_phi_4(ctx, network, length);
    Z3_ast phi_5 = create_phi_5(ctx, network, length);
    Z3_ast phi_6 = create_phi_6(ctx, network, length);

    // Combiner φ1 , φ2 , φ3 , φ4 , φ5 et φ6
    Z3_ast formulas[6] = {phi_1, phi_2, phi_3, phi_4, phi_5, phi_6};
    return Z3_mk_and(ctx, 6, formulas);

}

void tn_get_path_from_model(Z3_context ctx, Z3_model model, TunnelNetwork network, int bound, tn_step *path)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(bound);
    for (int pos = 0; pos < bound; pos++)
    {
        int src = -1;
        int src_height = -1;
        int tgt = -1;
        int tgt_height = -1;
        for (int n = 0; n < num_nodes; n++)
        {
            for (int height = 0; height < stack_size; height++)
            {
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, n, pos, height)))
                {
                    src = n;
                    src_height = height;
                }
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, n, pos + 1, height)))
                {
                    tgt = n;
                    tgt_height = height;
                }
            }
        }
        int action = 0;
        if (src_height == tgt_height)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
                action = transmit_4;
            else
                action = transmit_6;
        }
        else if (src_height == tgt_height - 1)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
            {
                if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                    action = push_4_4;
                else
                    action = push_4_6;
            }
            else if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                action = push_6_4;
            else
                action = push_6_6;
        }
        else if (src_height == tgt_height + 1)
        {
            {
                if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
                {
                    if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                        action = pop_4_4;
                    else
                        action = pop_6_4;
                }
                else if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                    action = pop_4_6;
                else
                    action = pop_6_6;
            }
        }
        path[pos] = tn_step_create(action, src, tgt);
    }
}

void tn_print_model(Z3_context ctx, Z3_model model, TunnelNetwork network, int bound)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(bound);
    for (int pos = 0; pos < bound + 1; pos++)
    {
        printf("At pos %d:\nState: ", pos);
        int num_seen = 0;
        for (int node = 0; node < num_nodes; node++)
        {
            for (int height = 0; height < stack_size; height++)
            {
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, node, pos, height)))
                {
                    printf("(%s,%d) ", tn_get_node_name(network, node), height);
                    num_seen++;
                }
            }
        }
        if (num_seen == 0)
            printf("No node at that position !\n");
        else
            printf("\n");
        if (num_seen > 1)
            printf("Several pair node,height!\n");
        printf("Stack: ");
        bool misdefined = false;
        bool above_top = false;
        for (int height = 0; height < stack_size; height++)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, height)))
            {
                if (value_of_var_in_model(ctx, model, tn_6_variable(ctx, pos, height)))
                {
                    printf("|X");
                    misdefined = true;
                }
                else
                {
                    printf("|4");
                    if (above_top)
                        misdefined = true;
                }
            }
            else if (value_of_var_in_model(ctx, model, tn_6_variable(ctx, pos, height)))
            {
                printf("|6");
                if (above_top)
                    misdefined = true;
            }
            else
            {
                printf("| ");
                above_top = true;
            }
        }
        printf("\n");
        if (misdefined)
            printf("Warning: ill-defined stack\n");
    }
    return;
}