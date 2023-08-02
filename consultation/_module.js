function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert(target, node, anchor) {
    target.insertBefore(node, anchor || null);
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function prevent_default(fn) {
    return function (event) {
        event.preventDefault();
        // @ts-ignore
        return fn.call(this, event);
    };
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
/**
 * List of attributes that should always be set through the attr method,
 * because updating them through the property setter doesn't work reliably.
 * In the example of `width`/`height`, the problem is that the setter only
 * accepts numeric values, but the attribute can also be set to a string like `50%`.
 * If this list becomes too big, rethink this approach.
 */
const always_set_through_set_attribute = ['width', 'height'];
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set && always_set_through_set_attribute.indexOf(key) === -1) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function find_comment(nodes, text, start) {
    for (let i = start; i < nodes.length; i += 1) {
        const node = nodes[i];
        if (node.nodeType === 8 /* comment node */ && node.textContent.trim() === text) {
            return i;
        }
    }
    return nodes.length;
}
function claim_html_tag(nodes, is_svg) {
    // find html opening tag
    const start_index = find_comment(nodes, 'HTML_TAG_START', 0);
    const end_index = find_comment(nodes, 'HTML_TAG_END', start_index);
    if (start_index === end_index) {
        return new HtmlTagHydration(undefined, is_svg);
    }
    init_claim_info(nodes);
    const html_tag_nodes = nodes.splice(start_index, end_index - start_index + 1);
    detach(html_tag_nodes[0]);
    detach(html_tag_nodes[html_tag_nodes.length - 1]);
    const claimed_nodes = html_tag_nodes.slice(1, html_tag_nodes.length - 1);
    for (const n of claimed_nodes) {
        n.claim_order = nodes.claim_info.total_claimed;
        nodes.claim_info.total_claimed += 1;
    }
    return new HtmlTagHydration(claimed_nodes, is_svg);
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}
class HtmlTag {
    constructor(is_svg = false) {
        this.is_svg = false;
        this.is_svg = is_svg;
        this.e = this.n = null;
    }
    c(html) {
        this.h(html);
    }
    m(html, target, anchor = null) {
        if (!this.e) {
            if (this.is_svg)
                this.e = svg_element(target.nodeName);
            /** #7364  target for <template> may be provided as #document-fragment(11) */
            else
                this.e = element((target.nodeType === 11 ? 'TEMPLATE' : target.nodeName));
            this.t = target.tagName !== 'TEMPLATE' ? target : target.content;
            this.c(html);
        }
        this.i(anchor);
    }
    h(html) {
        this.e.innerHTML = html;
        this.n = Array.from(this.e.nodeName === 'TEMPLATE' ? this.e.content.childNodes : this.e.childNodes);
    }
    i(anchor) {
        for (let i = 0; i < this.n.length; i += 1) {
            insert(this.t, this.n[i], anchor);
        }
    }
    p(html) {
        this.d();
        this.h(html);
        this.i(this.a);
    }
    d() {
        this.n.forEach(detach);
    }
}
class HtmlTagHydration extends HtmlTag {
    constructor(claimed_nodes, is_svg = false) {
        super(is_svg);
        this.e = this.n = null;
        this.l = claimed_nodes;
    }
    c(html) {
        if (this.l) {
            this.n = this.l;
        }
        else {
            super.c(html);
        }
    }
    i(anchor) {
        for (let i = 0; i < this.n.length; i += 1) {
            insert_hydration(this.t, this.n[i], anchor);
        }
    }
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.59.1 */

function create_fragment(ctx) {
	let style;
	let t;

	return {
		c() {
			style = element("style");
			t = text("/* Reset & standardize default styles */\n@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options */\n  --color-accent: #20bfa9;\n  --color-accent-2: #ff794d;\n\n  /* Base values */\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --border-color: #e1ecf0;\n}\n\n/* Root element (use instead of `body`) */\n#page {\n  font-family: system-ui, sans-serif;\n  color: #1d263a;\n  line-height: 1.2;\n  font-size: 1.125rem;\n  background: white;\n}\n\n/* Elements */\n.section-container {\n  max-width: 1250px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n\na.link {\n  line-height: 1.3;\n  font-weight: 500;\n  border-bottom: 2px solid;\n  transform: translateY(-2px); /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: 2.5rem;\n  line-height: 1.1;\n  font-weight: 600;\n}\n\n.subheading {\n  font-weight: 400;\n  line-height: 1.5;\n  opacity: 90%;\n}\n\n.button {\n  display: inline-flex;\n  align-items: center;\n  justify-content: center;\n  gap: 0.5rem;\n  color: white;\n  font-weight: 500;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 3rem;\n  padding: 15px 25px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0;\n}\n\n/* reset */\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }\n\n/* Content Section */\n.section .content {\n  max-width: 1200px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n.section .content p {\n    padding: 0.25rem 0;\n    line-height: 1.5;\n  }\n.section .content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n.section .content a.link {\n  }\n.section .content h1 {\n    font-size: 3rem;\n    font-weight: 700;\n    margin-bottom: 1rem;\n  }\n.section .content h2 {\n    font-size: 2.25rem;\n    font-weight: 600;\n    margin-bottom: 0.5rem;\n  }\n.section .content h3 {\n    font-size: 1.75rem;\n    font-weight: 600;\n    margin-bottom: 0.25rem;\n  }\n.section .content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.section .content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.section .content blockquote {\n    padding: 2rem;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }");
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-1vsfxrb', document.head);
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "/* Reset & standardize default styles */\n@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options */\n  --color-accent: #20bfa9;\n  --color-accent-2: #ff794d;\n\n  /* Base values */\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --border-color: #e1ecf0;\n}\n\n/* Root element (use instead of `body`) */\n#page {\n  font-family: system-ui, sans-serif;\n  color: #1d263a;\n  line-height: 1.2;\n  font-size: 1.125rem;\n  background: white;\n}\n\n/* Elements */\n.section-container {\n  max-width: 1250px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n\na.link {\n  line-height: 1.3;\n  font-weight: 500;\n  border-bottom: 2px solid;\n  transform: translateY(-2px); /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: 2.5rem;\n  line-height: 1.1;\n  font-weight: 600;\n}\n\n.subheading {\n  font-weight: 400;\n  line-height: 1.5;\n  opacity: 90%;\n}\n\n.button {\n  display: inline-flex;\n  align-items: center;\n  justify-content: center;\n  gap: 0.5rem;\n  color: white;\n  font-weight: 500;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 3rem;\n  padding: 15px 25px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0;\n}\n\n/* reset */\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }\n\n/* Content Section */\n.section .content {\n  max-width: 1200px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n.section .content p {\n    padding: 0.25rem 0;\n    line-height: 1.5;\n  }\n.section .content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n.section .content a.link {\n  }\n.section .content h1 {\n    font-size: 3rem;\n    font-weight: 700;\n    margin-bottom: 1rem;\n  }\n.section .content h2 {\n    font-size: 2.25rem;\n    font-weight: 600;\n    margin-bottom: 0.5rem;\n  }\n.section .content h3 {\n    font-size: 1.75rem;\n    font-weight: 600;\n    margin-bottom: 0.25rem;\n  }\n.section .content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.section .content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.section .content blockquote {\n    padding: 2rem;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
		},
		m(target, anchor) {
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { primary_cta } = $$props;
	let { footer_links } = $$props;
	let { company_description } = $$props;

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
		if ('primary_cta' in $$props) $$invalidate(2, primary_cta = $$props.primary_cta);
		if ('footer_links' in $$props) $$invalidate(3, footer_links = $$props.footer_links);
		if ('company_description' in $$props) $$invalidate(4, company_description = $$props.company_description);
	};

	return [logo, site_nav, primary_cta, footer_links, company_description];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance, create_fragment, safe_not_equal, {
			logo: 0,
			site_nav: 1,
			primary_cta: 2,
			footer_links: 3,
			company_description: 4
		});
	}
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});
function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}
function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}
function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}
function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}
function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}
const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  return data;
}
const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
      return true;
    }
  } catch (err) {
  }
  return false;
}
let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
  ...defaultIconTransformations
});
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}
const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  attributes.viewBox = box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString();
  return {
    attributes,
    body
  };
}
const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + suffix + "$3");
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}
const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}
function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};
function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage2 = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}
function removeCallback(storages, id) {
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}
function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
}
const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}
let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}
function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}
function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}
function emptyCallback() {
}
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix} = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}
const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}
function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}
function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}
const defaultExtendedIconCustomisations = {
  ...defaultIconCustomisations,
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  if (icon.body.indexOf("xlink:") === -1) {
    delete componentProps["xmlns:xlink"];
  }
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url
  };
  const size = (prop) => {
    const value = renderAttribs[prop];
    if (value) {
      styles[prop] = fixSize(value);
    }
  };
  size("width");
  size("height");
  Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.59.1 */

function create_if_block(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (113:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		 {
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
}

/* generated by Svelte v3.59.1 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].link;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].link;
	return child_ctx;
}

// (111:31) 
function create_if_block_4(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (109:6) {#if logo.title}
function create_if_block_3(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (116:6) {#each site_nav as { link }}
function create_each_block_1(ctx) {
	let a;
	let t_value = /*link*/ ctx[9].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-qh80cp");
			attr(a, "href", a_href_value = /*link*/ ctx[9].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[9].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[9].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (126:31) 
function create_if_block_2(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (124:6) {#if logo.title}
function create_if_block_1$1(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (136:4) {#if mobileNavOpen}
function create_if_block$1(ctx) {
	let nav;
	let t0;
	let a;
	let t1_value = /*primary_cta*/ ctx[2].label + "";
	let t1;
	let a_href_value;
	let t2;
	let button;
	let icon;
	let nav_transition;
	let current;
	let mounted;
	let dispose;
	let each_value = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	icon = new Component$1({ props: { height: "25", icon: "bi:x-lg" } });

	return {
		c() {
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t0 = space();
			a = element("a");
			t1 = text(t1_value);
			t2 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t0 = claim_space(nav_nodes);
			a = claim_element(nav_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t1 = claim_text(a_nodes, t1_value);
			a_nodes.forEach(detach);
			t2 = claim_space(nav_nodes);

			button = claim_element(nav_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*primary_cta*/ ctx[2].url);
			attr(a, "class", "button svelte-qh80cp");
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-qh80cp");
			attr(nav, "id", "popup");
			attr(nav, "class", "svelte-qh80cp");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t0);
			append_hydration(nav, a);
			append_hydration(a, t1);
			append_hydration(nav, t2);
			append_hydration(nav, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[7]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2) {
				each_value = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t0);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if ((!current || dirty & /*primary_cta*/ 4) && t1_value !== (t1_value = /*primary_cta*/ ctx[2].label + "")) set_data(t1, t1_value);

			if (!current || dirty & /*primary_cta*/ 4 && a_href_value !== (a_href_value = /*primary_cta*/ ctx[2].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, true);
				nav_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, false);
			nav_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (detaching && nav_transition) nav_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (138:8) {#each site_nav as { link }}
function create_each_block(ctx) {
	let a;
	let t_value = /*link*/ ctx[9].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[9].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[9].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[9].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$2(ctx) {
	let div2;
	let header;
	let div0;
	let a0;
	let t0;
	let nav;
	let t1;
	let a1;
	let t2_value = /*primary_cta*/ ctx[2].label + "";
	let t2;
	let a1_href_value;
	let t3;
	let div1;
	let a2;
	let t4;
	let button;
	let icon;
	let t5;
	let current;
	let mounted;
	let dispose;

	function select_block_type(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block_3;
		if (/*logo*/ ctx[0].image.url) return create_if_block_4;
	}

	let current_block_type = select_block_type(ctx);
	let if_block0 = current_block_type && current_block_type(ctx);
	let each_value_1 = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	function select_block_type_1(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block_1$1;
		if (/*logo*/ ctx[0].image.url) return create_if_block_2;
	}

	let current_block_type_1 = select_block_type_1(ctx);
	let if_block1 = current_block_type_1 && current_block_type_1(ctx);

	icon = new Component$1({
			props: { height: "30", icon: "eva:menu-outline" }
		});

	let if_block2 = /*mobileNavOpen*/ ctx[3] && create_if_block$1(ctx);

	return {
		c() {
			div2 = element("div");
			header = element("header");
			div0 = element("div");
			a0 = element("a");
			if (if_block0) if_block0.c();
			t0 = space();
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t1 = space();
			a1 = element("a");
			t2 = text(t2_value);
			t3 = space();
			div1 = element("div");
			a2 = element("a");
			if (if_block1) if_block1.c();
			t4 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t5 = space();
			if (if_block2) if_block2.c();
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			header = claim_element(div2_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a0 = claim_element(div0_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			if (if_block0) if_block0.l(a0_nodes);
			a0_nodes.forEach(detach);
			t0 = claim_space(div0_nodes);
			nav = claim_element(div0_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t1 = claim_space(nav_nodes);
			a1 = claim_element(nav_nodes, "A", { href: true, class: true });
			var a1_nodes = children(a1);
			t2 = claim_text(a1_nodes, t2_value);
			a1_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(header_nodes);
			div1 = claim_element(header_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a2 = claim_element(div1_nodes, "A", { href: true, class: true });
			var a2_nodes = children(a2);
			if (if_block1) if_block1.l(a2_nodes);
			a2_nodes.forEach(detach);
			t4 = claim_space(div1_nodes);
			button = claim_element(div1_nodes, "BUTTON", { id: true, "aria-label": true });
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			t5 = claim_space(div1_nodes);
			if (if_block2) if_block2.l(div1_nodes);
			div1_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "href", "/");
			attr(a0, "class", "logo svelte-qh80cp");
			attr(a1, "href", a1_href_value = /*primary_cta*/ ctx[2].url);
			attr(a1, "class", "button svelte-qh80cp");
			attr(nav, "class", "svelte-qh80cp");
			attr(div0, "class", "desktop-nav svelte-qh80cp");
			attr(a2, "href", "/");
			attr(a2, "class", "logo svelte-qh80cp");
			attr(button, "id", "open");
			attr(button, "aria-label", "Open mobile navigation");
			attr(div1, "class", "mobile-nav svelte-qh80cp");
			attr(header, "class", "section-container svelte-qh80cp");
			attr(div2, "class", "section");
			attr(div2, "id", "section-12bf3812");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, header);
			append_hydration(header, div0);
			append_hydration(div0, a0);
			if (if_block0) if_block0.m(a0, null);
			append_hydration(div0, t0);
			append_hydration(div0, nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t1);
			append_hydration(nav, a1);
			append_hydration(a1, t2);
			append_hydration(header, t3);
			append_hydration(header, div1);
			append_hydration(div1, a2);
			if (if_block1) if_block1.m(a2, null);
			append_hydration(div1, t4);
			append_hydration(div1, button);
			mount_component(icon, button, null);
			append_hydration(div1, t5);
			if (if_block2) if_block2.m(div1, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[6]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block0) {
				if_block0.p(ctx, dirty);
			} else {
				if (if_block0) if_block0.d(1);
				if_block0 = current_block_type && current_block_type(ctx);

				if (if_block0) {
					if_block0.c();
					if_block0.m(a0, null);
				}
			}

			if (dirty & /*site_nav*/ 2) {
				each_value_1 = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t1);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}

			if ((!current || dirty & /*primary_cta*/ 4) && t2_value !== (t2_value = /*primary_cta*/ ctx[2].label + "")) set_data(t2, t2_value);

			if (!current || dirty & /*primary_cta*/ 4 && a1_href_value !== (a1_href_value = /*primary_cta*/ ctx[2].url)) {
				attr(a1, "href", a1_href_value);
			}

			if (current_block_type_1 === (current_block_type_1 = select_block_type_1(ctx)) && if_block1) {
				if_block1.p(ctx, dirty);
			} else {
				if (if_block1) if_block1.d(1);
				if_block1 = current_block_type_1 && current_block_type_1(ctx);

				if (if_block1) {
					if_block1.c();
					if_block1.m(a2, null);
				}
			}

			if (/*mobileNavOpen*/ ctx[3]) {
				if (if_block2) {
					if_block2.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 8) {
						transition_in(if_block2, 1);
					}
				} else {
					if_block2 = create_if_block$1(ctx);
					if_block2.c();
					transition_in(if_block2, 1);
					if_block2.m(div1, null);
				}
			} else if (if_block2) {
				group_outros();

				transition_out(if_block2, 1, 1, () => {
					if_block2 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			transition_in(if_block2);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			transition_out(if_block2);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div2);

			if (if_block0) {
				if_block0.d();
			}

			destroy_each(each_blocks, detaching);

			if (if_block1) {
				if_block1.d();
			}

			destroy_component(icon);
			if (if_block2) if_block2.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { primary_cta } = $$props;
	let { footer_links } = $$props;
	let { company_description } = $$props;
	let mobileNavOpen = false;

	const click_handler = () => $$invalidate(3, mobileNavOpen = true);
	const click_handler_1 = () => $$invalidate(3, mobileNavOpen = false);

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
		if ('primary_cta' in $$props) $$invalidate(2, primary_cta = $$props.primary_cta);
		if ('footer_links' in $$props) $$invalidate(4, footer_links = $$props.footer_links);
		if ('company_description' in $$props) $$invalidate(5, company_description = $$props.company_description);
	};

	return [
		logo,
		site_nav,
		primary_cta,
		mobileNavOpen,
		footer_links,
		company_description,
		click_handler,
		click_handler_1
	];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
			logo: 0,
			site_nav: 1,
			primary_cta: 2,
			footer_links: 4,
			company_description: 5
		});
	}
}

var browser = typeof self == "object" ? self.FormData : window.FormData;

var global$1 = typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {};
function bind(fn, thisArg) {
  return function wrap() {
    return fn.apply(thisArg, arguments);
  };
}
const {toString} = Object.prototype;
const {getPrototypeOf} = Object;
const kindOf = ((cache) => (thing) => {
  const str = toString.call(thing);
  return cache[str] || (cache[str] = str.slice(8, -1).toLowerCase());
})(Object.create(null));
const kindOfTest = (type) => {
  type = type.toLowerCase();
  return (thing) => kindOf(thing) === type;
};
const typeOfTest = (type) => (thing) => typeof thing === type;
const {isArray} = Array;
const isUndefined = typeOfTest("undefined");
function isBuffer(val) {
  return val !== null && !isUndefined(val) && val.constructor !== null && !isUndefined(val.constructor) && isFunction(val.constructor.isBuffer) && val.constructor.isBuffer(val);
}
const isArrayBuffer = kindOfTest("ArrayBuffer");
function isArrayBufferView(val) {
  let result;
  if (typeof ArrayBuffer !== "undefined" && ArrayBuffer.isView) {
    result = ArrayBuffer.isView(val);
  } else {
    result = val && val.buffer && isArrayBuffer(val.buffer);
  }
  return result;
}
const isString = typeOfTest("string");
const isFunction = typeOfTest("function");
const isNumber = typeOfTest("number");
const isObject = (thing) => thing !== null && typeof thing === "object";
const isBoolean = (thing) => thing === true || thing === false;
const isPlainObject = (val) => {
  if (kindOf(val) !== "object") {
    return false;
  }
  const prototype2 = getPrototypeOf(val);
  return (prototype2 === null || prototype2 === Object.prototype || Object.getPrototypeOf(prototype2) === null) && !(Symbol.toStringTag in val) && !(Symbol.iterator in val);
};
const isDate = kindOfTest("Date");
const isFile = kindOfTest("File");
const isBlob = kindOfTest("Blob");
const isFileList = kindOfTest("FileList");
const isStream = (val) => isObject(val) && isFunction(val.pipe);
const isFormData = (thing) => {
  const pattern = "[object FormData]";
  return thing && (typeof FormData === "function" && thing instanceof FormData || toString.call(thing) === pattern || isFunction(thing.toString) && thing.toString() === pattern);
};
const isURLSearchParams = kindOfTest("URLSearchParams");
const trim = (str) => str.trim ? str.trim() : str.replace(/^[\s\uFEFF\xA0]+|[\s\uFEFF\xA0]+$/g, "");
function forEach(obj, fn, {allOwnKeys = false} = {}) {
  if (obj === null || typeof obj === "undefined") {
    return;
  }
  let i;
  let l;
  if (typeof obj !== "object") {
    obj = [obj];
  }
  if (isArray(obj)) {
    for (i = 0, l = obj.length; i < l; i++) {
      fn.call(null, obj[i], i, obj);
    }
  } else {
    const keys = allOwnKeys ? Object.getOwnPropertyNames(obj) : Object.keys(obj);
    const len = keys.length;
    let key;
    for (i = 0; i < len; i++) {
      key = keys[i];
      fn.call(null, obj[key], key, obj);
    }
  }
}
function findKey(obj, key) {
  key = key.toLowerCase();
  const keys = Object.keys(obj);
  let i = keys.length;
  let _key;
  while (i-- > 0) {
    _key = keys[i];
    if (key === _key.toLowerCase()) {
      return _key;
    }
  }
  return null;
}
const _global = typeof self === "undefined" ? typeof global$1 === "undefined" ? void 0 : global$1 : self;
const isContextDefined = (context) => !isUndefined(context) && context !== _global;
function merge() {
  const {caseless} = isContextDefined(this) && this || {};
  const result = {};
  const assignValue = (val, key) => {
    const targetKey = caseless && findKey(result, key) || key;
    if (isPlainObject(result[targetKey]) && isPlainObject(val)) {
      result[targetKey] = merge(result[targetKey], val);
    } else if (isPlainObject(val)) {
      result[targetKey] = merge({}, val);
    } else if (isArray(val)) {
      result[targetKey] = val.slice();
    } else {
      result[targetKey] = val;
    }
  };
  for (let i = 0, l = arguments.length; i < l; i++) {
    arguments[i] && forEach(arguments[i], assignValue);
  }
  return result;
}
const extend = (a, b, thisArg, {allOwnKeys} = {}) => {
  forEach(b, (val, key) => {
    if (thisArg && isFunction(val)) {
      a[key] = bind(val, thisArg);
    } else {
      a[key] = val;
    }
  }, {allOwnKeys});
  return a;
};
const stripBOM = (content) => {
  if (content.charCodeAt(0) === 65279) {
    content = content.slice(1);
  }
  return content;
};
const inherits = (constructor, superConstructor, props, descriptors2) => {
  constructor.prototype = Object.create(superConstructor.prototype, descriptors2);
  constructor.prototype.constructor = constructor;
  Object.defineProperty(constructor, "super", {
    value: superConstructor.prototype
  });
  props && Object.assign(constructor.prototype, props);
};
const toFlatObject = (sourceObj, destObj, filter2, propFilter) => {
  let props;
  let i;
  let prop;
  const merged = {};
  destObj = destObj || {};
  if (sourceObj == null)
    return destObj;
  do {
    props = Object.getOwnPropertyNames(sourceObj);
    i = props.length;
    while (i-- > 0) {
      prop = props[i];
      if ((!propFilter || propFilter(prop, sourceObj, destObj)) && !merged[prop]) {
        destObj[prop] = sourceObj[prop];
        merged[prop] = true;
      }
    }
    sourceObj = filter2 !== false && getPrototypeOf(sourceObj);
  } while (sourceObj && (!filter2 || filter2(sourceObj, destObj)) && sourceObj !== Object.prototype);
  return destObj;
};
const endsWith = (str, searchString, position) => {
  str = String(str);
  if (position === void 0 || position > str.length) {
    position = str.length;
  }
  position -= searchString.length;
  const lastIndex = str.indexOf(searchString, position);
  return lastIndex !== -1 && lastIndex === position;
};
const toArray = (thing) => {
  if (!thing)
    return null;
  if (isArray(thing))
    return thing;
  let i = thing.length;
  if (!isNumber(i))
    return null;
  const arr = new Array(i);
  while (i-- > 0) {
    arr[i] = thing[i];
  }
  return arr;
};
const isTypedArray = ((TypedArray) => {
  return (thing) => {
    return TypedArray && thing instanceof TypedArray;
  };
})(typeof Uint8Array !== "undefined" && getPrototypeOf(Uint8Array));
const forEachEntry = (obj, fn) => {
  const generator = obj && obj[Symbol.iterator];
  const iterator = generator.call(obj);
  let result;
  while ((result = iterator.next()) && !result.done) {
    const pair = result.value;
    fn.call(obj, pair[0], pair[1]);
  }
};
const matchAll = (regExp, str) => {
  let matches;
  const arr = [];
  while ((matches = regExp.exec(str)) !== null) {
    arr.push(matches);
  }
  return arr;
};
const isHTMLForm = kindOfTest("HTMLFormElement");
const toCamelCase = (str) => {
  return str.toLowerCase().replace(/[_-\s]([a-z\d])(\w*)/g, function replacer(m, p1, p2) {
    return p1.toUpperCase() + p2;
  });
};
const hasOwnProperty = (({hasOwnProperty: hasOwnProperty2}) => (obj, prop) => hasOwnProperty2.call(obj, prop))(Object.prototype);
const isRegExp = kindOfTest("RegExp");
const reduceDescriptors = (obj, reducer) => {
  const descriptors2 = Object.getOwnPropertyDescriptors(obj);
  const reducedDescriptors = {};
  forEach(descriptors2, (descriptor, name) => {
    if (reducer(descriptor, name, obj) !== false) {
      reducedDescriptors[name] = descriptor;
    }
  });
  Object.defineProperties(obj, reducedDescriptors);
};
const freezeMethods = (obj) => {
  reduceDescriptors(obj, (descriptor, name) => {
    if (isFunction(obj) && ["arguments", "caller", "callee"].indexOf(name) !== -1) {
      return false;
    }
    const value = obj[name];
    if (!isFunction(value))
      return;
    descriptor.enumerable = false;
    if ("writable" in descriptor) {
      descriptor.writable = false;
      return;
    }
    if (!descriptor.set) {
      descriptor.set = () => {
        throw Error("Can not rewrite read-only method '" + name + "'");
      };
    }
  });
};
const toObjectSet = (arrayOrString, delimiter) => {
  const obj = {};
  const define = (arr) => {
    arr.forEach((value) => {
      obj[value] = true;
    });
  };
  isArray(arrayOrString) ? define(arrayOrString) : define(String(arrayOrString).split(delimiter));
  return obj;
};
const noop$1 = () => {
};
const toFiniteNumber = (value, defaultValue) => {
  value = +value;
  return Number.isFinite(value) ? value : defaultValue;
};
const toJSONObject = (obj) => {
  const stack = new Array(10);
  const visit = (source, i) => {
    if (isObject(source)) {
      if (stack.indexOf(source) >= 0) {
        return;
      }
      if (!("toJSON" in source)) {
        stack[i] = source;
        const target = isArray(source) ? [] : {};
        forEach(source, (value, key) => {
          const reducedValue = visit(value, i + 1);
          !isUndefined(reducedValue) && (target[key] = reducedValue);
        });
        stack[i] = void 0;
        return target;
      }
    }
    return source;
  };
  return visit(obj, 0);
};
var utils = {
  isArray,
  isArrayBuffer,
  isBuffer,
  isFormData,
  isArrayBufferView,
  isString,
  isNumber,
  isBoolean,
  isObject,
  isPlainObject,
  isUndefined,
  isDate,
  isFile,
  isBlob,
  isRegExp,
  isFunction,
  isStream,
  isURLSearchParams,
  isTypedArray,
  isFileList,
  forEach,
  merge,
  extend,
  trim,
  stripBOM,
  inherits,
  toFlatObject,
  kindOf,
  kindOfTest,
  endsWith,
  toArray,
  forEachEntry,
  matchAll,
  isHTMLForm,
  hasOwnProperty,
  hasOwnProp: hasOwnProperty,
  reduceDescriptors,
  freezeMethods,
  toObjectSet,
  toCamelCase,
  noop: noop$1,
  toFiniteNumber,
  findKey,
  global: _global,
  isContextDefined,
  toJSONObject
};
var lookup = [];
var revLookup = [];
var Arr = typeof Uint8Array !== "undefined" ? Uint8Array : Array;
var inited = false;
function init$1() {
  inited = true;
  var code = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  for (var i = 0, len = code.length; i < len; ++i) {
    lookup[i] = code[i];
    revLookup[code.charCodeAt(i)] = i;
  }
  revLookup["-".charCodeAt(0)] = 62;
  revLookup["_".charCodeAt(0)] = 63;
}
function toByteArray(b64) {
  if (!inited) {
    init$1();
  }
  var i, j, l, tmp, placeHolders, arr;
  var len = b64.length;
  if (len % 4 > 0) {
    throw new Error("Invalid string. Length must be a multiple of 4");
  }
  placeHolders = b64[len - 2] === "=" ? 2 : b64[len - 1] === "=" ? 1 : 0;
  arr = new Arr(len * 3 / 4 - placeHolders);
  l = placeHolders > 0 ? len - 4 : len;
  var L = 0;
  for (i = 0, j = 0; i < l; i += 4, j += 3) {
    tmp = revLookup[b64.charCodeAt(i)] << 18 | revLookup[b64.charCodeAt(i + 1)] << 12 | revLookup[b64.charCodeAt(i + 2)] << 6 | revLookup[b64.charCodeAt(i + 3)];
    arr[L++] = tmp >> 16 & 255;
    arr[L++] = tmp >> 8 & 255;
    arr[L++] = tmp & 255;
  }
  if (placeHolders === 2) {
    tmp = revLookup[b64.charCodeAt(i)] << 2 | revLookup[b64.charCodeAt(i + 1)] >> 4;
    arr[L++] = tmp & 255;
  } else if (placeHolders === 1) {
    tmp = revLookup[b64.charCodeAt(i)] << 10 | revLookup[b64.charCodeAt(i + 1)] << 4 | revLookup[b64.charCodeAt(i + 2)] >> 2;
    arr[L++] = tmp >> 8 & 255;
    arr[L++] = tmp & 255;
  }
  return arr;
}
function tripletToBase64(num) {
  return lookup[num >> 18 & 63] + lookup[num >> 12 & 63] + lookup[num >> 6 & 63] + lookup[num & 63];
}
function encodeChunk(uint8, start, end) {
  var tmp;
  var output = [];
  for (var i = start; i < end; i += 3) {
    tmp = (uint8[i] << 16) + (uint8[i + 1] << 8) + uint8[i + 2];
    output.push(tripletToBase64(tmp));
  }
  return output.join("");
}
function fromByteArray(uint8) {
  if (!inited) {
    init$1();
  }
  var tmp;
  var len = uint8.length;
  var extraBytes = len % 3;
  var output = "";
  var parts = [];
  var maxChunkLength = 16383;
  for (var i = 0, len2 = len - extraBytes; i < len2; i += maxChunkLength) {
    parts.push(encodeChunk(uint8, i, i + maxChunkLength > len2 ? len2 : i + maxChunkLength));
  }
  if (extraBytes === 1) {
    tmp = uint8[len - 1];
    output += lookup[tmp >> 2];
    output += lookup[tmp << 4 & 63];
    output += "==";
  } else if (extraBytes === 2) {
    tmp = (uint8[len - 2] << 8) + uint8[len - 1];
    output += lookup[tmp >> 10];
    output += lookup[tmp >> 4 & 63];
    output += lookup[tmp << 2 & 63];
    output += "=";
  }
  parts.push(output);
  return parts.join("");
}
function read(buffer, offset, isLE, mLen, nBytes) {
  var e, m;
  var eLen = nBytes * 8 - mLen - 1;
  var eMax = (1 << eLen) - 1;
  var eBias = eMax >> 1;
  var nBits = -7;
  var i = isLE ? nBytes - 1 : 0;
  var d = isLE ? -1 : 1;
  var s = buffer[offset + i];
  i += d;
  e = s & (1 << -nBits) - 1;
  s >>= -nBits;
  nBits += eLen;
  for (; nBits > 0; e = e * 256 + buffer[offset + i], i += d, nBits -= 8) {
  }
  m = e & (1 << -nBits) - 1;
  e >>= -nBits;
  nBits += mLen;
  for (; nBits > 0; m = m * 256 + buffer[offset + i], i += d, nBits -= 8) {
  }
  if (e === 0) {
    e = 1 - eBias;
  } else if (e === eMax) {
    return m ? NaN : (s ? -1 : 1) * Infinity;
  } else {
    m = m + Math.pow(2, mLen);
    e = e - eBias;
  }
  return (s ? -1 : 1) * m * Math.pow(2, e - mLen);
}
function write(buffer, value, offset, isLE, mLen, nBytes) {
  var e, m, c;
  var eLen = nBytes * 8 - mLen - 1;
  var eMax = (1 << eLen) - 1;
  var eBias = eMax >> 1;
  var rt = mLen === 23 ? Math.pow(2, -24) - Math.pow(2, -77) : 0;
  var i = isLE ? 0 : nBytes - 1;
  var d = isLE ? 1 : -1;
  var s = value < 0 || value === 0 && 1 / value < 0 ? 1 : 0;
  value = Math.abs(value);
  if (isNaN(value) || value === Infinity) {
    m = isNaN(value) ? 1 : 0;
    e = eMax;
  } else {
    e = Math.floor(Math.log(value) / Math.LN2);
    if (value * (c = Math.pow(2, -e)) < 1) {
      e--;
      c *= 2;
    }
    if (e + eBias >= 1) {
      value += rt / c;
    } else {
      value += rt * Math.pow(2, 1 - eBias);
    }
    if (value * c >= 2) {
      e++;
      c /= 2;
    }
    if (e + eBias >= eMax) {
      m = 0;
      e = eMax;
    } else if (e + eBias >= 1) {
      m = (value * c - 1) * Math.pow(2, mLen);
      e = e + eBias;
    } else {
      m = value * Math.pow(2, eBias - 1) * Math.pow(2, mLen);
      e = 0;
    }
  }
  for (; mLen >= 8; buffer[offset + i] = m & 255, i += d, m /= 256, mLen -= 8) {
  }
  e = e << mLen | m;
  eLen += mLen;
  for (; eLen > 0; buffer[offset + i] = e & 255, i += d, e /= 256, eLen -= 8) {
  }
  buffer[offset + i - d] |= s * 128;
}
var toString$1 = {}.toString;
var isArray$1 = Array.isArray || function(arr) {
  return toString$1.call(arr) == "[object Array]";
};
/*!
 * The buffer module from node.js, for the browser.
 *
 * @author   Feross Aboukhadijeh <feross@feross.org> <http://feross.org>
 * @license  MIT
 */
var INSPECT_MAX_BYTES = 50;
Buffer.TYPED_ARRAY_SUPPORT = global$1.TYPED_ARRAY_SUPPORT !== void 0 ? global$1.TYPED_ARRAY_SUPPORT : true;
function kMaxLength() {
  return Buffer.TYPED_ARRAY_SUPPORT ? 2147483647 : 1073741823;
}
function createBuffer(that, length) {
  if (kMaxLength() < length) {
    throw new RangeError("Invalid typed array length");
  }
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    that = new Uint8Array(length);
    that.__proto__ = Buffer.prototype;
  } else {
    if (that === null) {
      that = new Buffer(length);
    }
    that.length = length;
  }
  return that;
}
function Buffer(arg, encodingOrOffset, length) {
  if (!Buffer.TYPED_ARRAY_SUPPORT && !(this instanceof Buffer)) {
    return new Buffer(arg, encodingOrOffset, length);
  }
  if (typeof arg === "number") {
    if (typeof encodingOrOffset === "string") {
      throw new Error("If encoding is specified then the first argument must be a string");
    }
    return allocUnsafe(this, arg);
  }
  return from(this, arg, encodingOrOffset, length);
}
Buffer.poolSize = 8192;
Buffer._augment = function(arr) {
  arr.__proto__ = Buffer.prototype;
  return arr;
};
function from(that, value, encodingOrOffset, length) {
  if (typeof value === "number") {
    throw new TypeError('"value" argument must not be a number');
  }
  if (typeof ArrayBuffer !== "undefined" && value instanceof ArrayBuffer) {
    return fromArrayBuffer(that, value, encodingOrOffset, length);
  }
  if (typeof value === "string") {
    return fromString(that, value, encodingOrOffset);
  }
  return fromObject(that, value);
}
Buffer.from = function(value, encodingOrOffset, length) {
  return from(null, value, encodingOrOffset, length);
};
if (Buffer.TYPED_ARRAY_SUPPORT) {
  Buffer.prototype.__proto__ = Uint8Array.prototype;
  Buffer.__proto__ = Uint8Array;
}
function assertSize(size) {
  if (typeof size !== "number") {
    throw new TypeError('"size" argument must be a number');
  } else if (size < 0) {
    throw new RangeError('"size" argument must not be negative');
  }
}
function alloc(that, size, fill2, encoding) {
  assertSize(size);
  if (size <= 0) {
    return createBuffer(that, size);
  }
  if (fill2 !== void 0) {
    return typeof encoding === "string" ? createBuffer(that, size).fill(fill2, encoding) : createBuffer(that, size).fill(fill2);
  }
  return createBuffer(that, size);
}
Buffer.alloc = function(size, fill2, encoding) {
  return alloc(null, size, fill2, encoding);
};
function allocUnsafe(that, size) {
  assertSize(size);
  that = createBuffer(that, size < 0 ? 0 : checked(size) | 0);
  if (!Buffer.TYPED_ARRAY_SUPPORT) {
    for (var i = 0; i < size; ++i) {
      that[i] = 0;
    }
  }
  return that;
}
Buffer.allocUnsafe = function(size) {
  return allocUnsafe(null, size);
};
Buffer.allocUnsafeSlow = function(size) {
  return allocUnsafe(null, size);
};
function fromString(that, string, encoding) {
  if (typeof encoding !== "string" || encoding === "") {
    encoding = "utf8";
  }
  if (!Buffer.isEncoding(encoding)) {
    throw new TypeError('"encoding" must be a valid string encoding');
  }
  var length = byteLength(string, encoding) | 0;
  that = createBuffer(that, length);
  var actual = that.write(string, encoding);
  if (actual !== length) {
    that = that.slice(0, actual);
  }
  return that;
}
function fromArrayLike(that, array) {
  var length = array.length < 0 ? 0 : checked(array.length) | 0;
  that = createBuffer(that, length);
  for (var i = 0; i < length; i += 1) {
    that[i] = array[i] & 255;
  }
  return that;
}
function fromArrayBuffer(that, array, byteOffset, length) {
  array.byteLength;
  if (byteOffset < 0 || array.byteLength < byteOffset) {
    throw new RangeError("'offset' is out of bounds");
  }
  if (array.byteLength < byteOffset + (length || 0)) {
    throw new RangeError("'length' is out of bounds");
  }
  if (byteOffset === void 0 && length === void 0) {
    array = new Uint8Array(array);
  } else if (length === void 0) {
    array = new Uint8Array(array, byteOffset);
  } else {
    array = new Uint8Array(array, byteOffset, length);
  }
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    that = array;
    that.__proto__ = Buffer.prototype;
  } else {
    that = fromArrayLike(that, array);
  }
  return that;
}
function fromObject(that, obj) {
  if (internalIsBuffer(obj)) {
    var len = checked(obj.length) | 0;
    that = createBuffer(that, len);
    if (that.length === 0) {
      return that;
    }
    obj.copy(that, 0, 0, len);
    return that;
  }
  if (obj) {
    if (typeof ArrayBuffer !== "undefined" && obj.buffer instanceof ArrayBuffer || "length" in obj) {
      if (typeof obj.length !== "number" || isnan(obj.length)) {
        return createBuffer(that, 0);
      }
      return fromArrayLike(that, obj);
    }
    if (obj.type === "Buffer" && isArray$1(obj.data)) {
      return fromArrayLike(that, obj.data);
    }
  }
  throw new TypeError("First argument must be a string, Buffer, ArrayBuffer, Array, or array-like object.");
}
function checked(length) {
  if (length >= kMaxLength()) {
    throw new RangeError("Attempt to allocate Buffer larger than maximum size: 0x" + kMaxLength().toString(16) + " bytes");
  }
  return length | 0;
}
Buffer.isBuffer = isBuffer$1;
function internalIsBuffer(b) {
  return !!(b != null && b._isBuffer);
}
Buffer.compare = function compare(a, b) {
  if (!internalIsBuffer(a) || !internalIsBuffer(b)) {
    throw new TypeError("Arguments must be Buffers");
  }
  if (a === b)
    return 0;
  var x = a.length;
  var y = b.length;
  for (var i = 0, len = Math.min(x, y); i < len; ++i) {
    if (a[i] !== b[i]) {
      x = a[i];
      y = b[i];
      break;
    }
  }
  if (x < y)
    return -1;
  if (y < x)
    return 1;
  return 0;
};
Buffer.isEncoding = function isEncoding(encoding) {
  switch (String(encoding).toLowerCase()) {
    case "hex":
    case "utf8":
    case "utf-8":
    case "ascii":
    case "latin1":
    case "binary":
    case "base64":
    case "ucs2":
    case "ucs-2":
    case "utf16le":
    case "utf-16le":
      return true;
    default:
      return false;
  }
};
Buffer.concat = function concat(list, length) {
  if (!isArray$1(list)) {
    throw new TypeError('"list" argument must be an Array of Buffers');
  }
  if (list.length === 0) {
    return Buffer.alloc(0);
  }
  var i;
  if (length === void 0) {
    length = 0;
    for (i = 0; i < list.length; ++i) {
      length += list[i].length;
    }
  }
  var buffer = Buffer.allocUnsafe(length);
  var pos = 0;
  for (i = 0; i < list.length; ++i) {
    var buf = list[i];
    if (!internalIsBuffer(buf)) {
      throw new TypeError('"list" argument must be an Array of Buffers');
    }
    buf.copy(buffer, pos);
    pos += buf.length;
  }
  return buffer;
};
function byteLength(string, encoding) {
  if (internalIsBuffer(string)) {
    return string.length;
  }
  if (typeof ArrayBuffer !== "undefined" && typeof ArrayBuffer.isView === "function" && (ArrayBuffer.isView(string) || string instanceof ArrayBuffer)) {
    return string.byteLength;
  }
  if (typeof string !== "string") {
    string = "" + string;
  }
  var len = string.length;
  if (len === 0)
    return 0;
  var loweredCase = false;
  for (; ; ) {
    switch (encoding) {
      case "ascii":
      case "latin1":
      case "binary":
        return len;
      case "utf8":
      case "utf-8":
      case void 0:
        return utf8ToBytes(string).length;
      case "ucs2":
      case "ucs-2":
      case "utf16le":
      case "utf-16le":
        return len * 2;
      case "hex":
        return len >>> 1;
      case "base64":
        return base64ToBytes(string).length;
      default:
        if (loweredCase)
          return utf8ToBytes(string).length;
        encoding = ("" + encoding).toLowerCase();
        loweredCase = true;
    }
  }
}
Buffer.byteLength = byteLength;
function slowToString(encoding, start, end) {
  var loweredCase = false;
  if (start === void 0 || start < 0) {
    start = 0;
  }
  if (start > this.length) {
    return "";
  }
  if (end === void 0 || end > this.length) {
    end = this.length;
  }
  if (end <= 0) {
    return "";
  }
  end >>>= 0;
  start >>>= 0;
  if (end <= start) {
    return "";
  }
  if (!encoding)
    encoding = "utf8";
  while (true) {
    switch (encoding) {
      case "hex":
        return hexSlice(this, start, end);
      case "utf8":
      case "utf-8":
        return utf8Slice(this, start, end);
      case "ascii":
        return asciiSlice(this, start, end);
      case "latin1":
      case "binary":
        return latin1Slice(this, start, end);
      case "base64":
        return base64Slice(this, start, end);
      case "ucs2":
      case "ucs-2":
      case "utf16le":
      case "utf-16le":
        return utf16leSlice(this, start, end);
      default:
        if (loweredCase)
          throw new TypeError("Unknown encoding: " + encoding);
        encoding = (encoding + "").toLowerCase();
        loweredCase = true;
    }
  }
}
Buffer.prototype._isBuffer = true;
function swap(b, n, m) {
  var i = b[n];
  b[n] = b[m];
  b[m] = i;
}
Buffer.prototype.swap16 = function swap16() {
  var len = this.length;
  if (len % 2 !== 0) {
    throw new RangeError("Buffer size must be a multiple of 16-bits");
  }
  for (var i = 0; i < len; i += 2) {
    swap(this, i, i + 1);
  }
  return this;
};
Buffer.prototype.swap32 = function swap32() {
  var len = this.length;
  if (len % 4 !== 0) {
    throw new RangeError("Buffer size must be a multiple of 32-bits");
  }
  for (var i = 0; i < len; i += 4) {
    swap(this, i, i + 3);
    swap(this, i + 1, i + 2);
  }
  return this;
};
Buffer.prototype.swap64 = function swap64() {
  var len = this.length;
  if (len % 8 !== 0) {
    throw new RangeError("Buffer size must be a multiple of 64-bits");
  }
  for (var i = 0; i < len; i += 8) {
    swap(this, i, i + 7);
    swap(this, i + 1, i + 6);
    swap(this, i + 2, i + 5);
    swap(this, i + 3, i + 4);
  }
  return this;
};
Buffer.prototype.toString = function toString2() {
  var length = this.length | 0;
  if (length === 0)
    return "";
  if (arguments.length === 0)
    return utf8Slice(this, 0, length);
  return slowToString.apply(this, arguments);
};
Buffer.prototype.equals = function equals(b) {
  if (!internalIsBuffer(b))
    throw new TypeError("Argument must be a Buffer");
  if (this === b)
    return true;
  return Buffer.compare(this, b) === 0;
};
Buffer.prototype.inspect = function inspect() {
  var str = "";
  var max = INSPECT_MAX_BYTES;
  if (this.length > 0) {
    str = this.toString("hex", 0, max).match(/.{2}/g).join(" ");
    if (this.length > max)
      str += " ... ";
  }
  return "<Buffer " + str + ">";
};
Buffer.prototype.compare = function compare2(target, start, end, thisStart, thisEnd) {
  if (!internalIsBuffer(target)) {
    throw new TypeError("Argument must be a Buffer");
  }
  if (start === void 0) {
    start = 0;
  }
  if (end === void 0) {
    end = target ? target.length : 0;
  }
  if (thisStart === void 0) {
    thisStart = 0;
  }
  if (thisEnd === void 0) {
    thisEnd = this.length;
  }
  if (start < 0 || end > target.length || thisStart < 0 || thisEnd > this.length) {
    throw new RangeError("out of range index");
  }
  if (thisStart >= thisEnd && start >= end) {
    return 0;
  }
  if (thisStart >= thisEnd) {
    return -1;
  }
  if (start >= end) {
    return 1;
  }
  start >>>= 0;
  end >>>= 0;
  thisStart >>>= 0;
  thisEnd >>>= 0;
  if (this === target)
    return 0;
  var x = thisEnd - thisStart;
  var y = end - start;
  var len = Math.min(x, y);
  var thisCopy = this.slice(thisStart, thisEnd);
  var targetCopy = target.slice(start, end);
  for (var i = 0; i < len; ++i) {
    if (thisCopy[i] !== targetCopy[i]) {
      x = thisCopy[i];
      y = targetCopy[i];
      break;
    }
  }
  if (x < y)
    return -1;
  if (y < x)
    return 1;
  return 0;
};
function bidirectionalIndexOf(buffer, val, byteOffset, encoding, dir) {
  if (buffer.length === 0)
    return -1;
  if (typeof byteOffset === "string") {
    encoding = byteOffset;
    byteOffset = 0;
  } else if (byteOffset > 2147483647) {
    byteOffset = 2147483647;
  } else if (byteOffset < -2147483648) {
    byteOffset = -2147483648;
  }
  byteOffset = +byteOffset;
  if (isNaN(byteOffset)) {
    byteOffset = dir ? 0 : buffer.length - 1;
  }
  if (byteOffset < 0)
    byteOffset = buffer.length + byteOffset;
  if (byteOffset >= buffer.length) {
    if (dir)
      return -1;
    else
      byteOffset = buffer.length - 1;
  } else if (byteOffset < 0) {
    if (dir)
      byteOffset = 0;
    else
      return -1;
  }
  if (typeof val === "string") {
    val = Buffer.from(val, encoding);
  }
  if (internalIsBuffer(val)) {
    if (val.length === 0) {
      return -1;
    }
    return arrayIndexOf(buffer, val, byteOffset, encoding, dir);
  } else if (typeof val === "number") {
    val = val & 255;
    if (Buffer.TYPED_ARRAY_SUPPORT && typeof Uint8Array.prototype.indexOf === "function") {
      if (dir) {
        return Uint8Array.prototype.indexOf.call(buffer, val, byteOffset);
      } else {
        return Uint8Array.prototype.lastIndexOf.call(buffer, val, byteOffset);
      }
    }
    return arrayIndexOf(buffer, [val], byteOffset, encoding, dir);
  }
  throw new TypeError("val must be string, number or Buffer");
}
function arrayIndexOf(arr, val, byteOffset, encoding, dir) {
  var indexSize = 1;
  var arrLength = arr.length;
  var valLength = val.length;
  if (encoding !== void 0) {
    encoding = String(encoding).toLowerCase();
    if (encoding === "ucs2" || encoding === "ucs-2" || encoding === "utf16le" || encoding === "utf-16le") {
      if (arr.length < 2 || val.length < 2) {
        return -1;
      }
      indexSize = 2;
      arrLength /= 2;
      valLength /= 2;
      byteOffset /= 2;
    }
  }
  function read2(buf, i2) {
    if (indexSize === 1) {
      return buf[i2];
    } else {
      return buf.readUInt16BE(i2 * indexSize);
    }
  }
  var i;
  if (dir) {
    var foundIndex = -1;
    for (i = byteOffset; i < arrLength; i++) {
      if (read2(arr, i) === read2(val, foundIndex === -1 ? 0 : i - foundIndex)) {
        if (foundIndex === -1)
          foundIndex = i;
        if (i - foundIndex + 1 === valLength)
          return foundIndex * indexSize;
      } else {
        if (foundIndex !== -1)
          i -= i - foundIndex;
        foundIndex = -1;
      }
    }
  } else {
    if (byteOffset + valLength > arrLength)
      byteOffset = arrLength - valLength;
    for (i = byteOffset; i >= 0; i--) {
      var found = true;
      for (var j = 0; j < valLength; j++) {
        if (read2(arr, i + j) !== read2(val, j)) {
          found = false;
          break;
        }
      }
      if (found)
        return i;
    }
  }
  return -1;
}
Buffer.prototype.includes = function includes(val, byteOffset, encoding) {
  return this.indexOf(val, byteOffset, encoding) !== -1;
};
Buffer.prototype.indexOf = function indexOf(val, byteOffset, encoding) {
  return bidirectionalIndexOf(this, val, byteOffset, encoding, true);
};
Buffer.prototype.lastIndexOf = function lastIndexOf(val, byteOffset, encoding) {
  return bidirectionalIndexOf(this, val, byteOffset, encoding, false);
};
function hexWrite(buf, string, offset, length) {
  offset = Number(offset) || 0;
  var remaining = buf.length - offset;
  if (!length) {
    length = remaining;
  } else {
    length = Number(length);
    if (length > remaining) {
      length = remaining;
    }
  }
  var strLen = string.length;
  if (strLen % 2 !== 0)
    throw new TypeError("Invalid hex string");
  if (length > strLen / 2) {
    length = strLen / 2;
  }
  for (var i = 0; i < length; ++i) {
    var parsed = parseInt(string.substr(i * 2, 2), 16);
    if (isNaN(parsed))
      return i;
    buf[offset + i] = parsed;
  }
  return i;
}
function utf8Write(buf, string, offset, length) {
  return blitBuffer(utf8ToBytes(string, buf.length - offset), buf, offset, length);
}
function asciiWrite(buf, string, offset, length) {
  return blitBuffer(asciiToBytes(string), buf, offset, length);
}
function latin1Write(buf, string, offset, length) {
  return asciiWrite(buf, string, offset, length);
}
function base64Write(buf, string, offset, length) {
  return blitBuffer(base64ToBytes(string), buf, offset, length);
}
function ucs2Write(buf, string, offset, length) {
  return blitBuffer(utf16leToBytes(string, buf.length - offset), buf, offset, length);
}
Buffer.prototype.write = function write2(string, offset, length, encoding) {
  if (offset === void 0) {
    encoding = "utf8";
    length = this.length;
    offset = 0;
  } else if (length === void 0 && typeof offset === "string") {
    encoding = offset;
    length = this.length;
    offset = 0;
  } else if (isFinite(offset)) {
    offset = offset | 0;
    if (isFinite(length)) {
      length = length | 0;
      if (encoding === void 0)
        encoding = "utf8";
    } else {
      encoding = length;
      length = void 0;
    }
  } else {
    throw new Error("Buffer.write(string, encoding, offset[, length]) is no longer supported");
  }
  var remaining = this.length - offset;
  if (length === void 0 || length > remaining)
    length = remaining;
  if (string.length > 0 && (length < 0 || offset < 0) || offset > this.length) {
    throw new RangeError("Attempt to write outside buffer bounds");
  }
  if (!encoding)
    encoding = "utf8";
  var loweredCase = false;
  for (; ; ) {
    switch (encoding) {
      case "hex":
        return hexWrite(this, string, offset, length);
      case "utf8":
      case "utf-8":
        return utf8Write(this, string, offset, length);
      case "ascii":
        return asciiWrite(this, string, offset, length);
      case "latin1":
      case "binary":
        return latin1Write(this, string, offset, length);
      case "base64":
        return base64Write(this, string, offset, length);
      case "ucs2":
      case "ucs-2":
      case "utf16le":
      case "utf-16le":
        return ucs2Write(this, string, offset, length);
      default:
        if (loweredCase)
          throw new TypeError("Unknown encoding: " + encoding);
        encoding = ("" + encoding).toLowerCase();
        loweredCase = true;
    }
  }
};
Buffer.prototype.toJSON = function toJSON() {
  return {
    type: "Buffer",
    data: Array.prototype.slice.call(this._arr || this, 0)
  };
};
function base64Slice(buf, start, end) {
  if (start === 0 && end === buf.length) {
    return fromByteArray(buf);
  } else {
    return fromByteArray(buf.slice(start, end));
  }
}
function utf8Slice(buf, start, end) {
  end = Math.min(buf.length, end);
  var res = [];
  var i = start;
  while (i < end) {
    var firstByte = buf[i];
    var codePoint = null;
    var bytesPerSequence = firstByte > 239 ? 4 : firstByte > 223 ? 3 : firstByte > 191 ? 2 : 1;
    if (i + bytesPerSequence <= end) {
      var secondByte, thirdByte, fourthByte, tempCodePoint;
      switch (bytesPerSequence) {
        case 1:
          if (firstByte < 128) {
            codePoint = firstByte;
          }
          break;
        case 2:
          secondByte = buf[i + 1];
          if ((secondByte & 192) === 128) {
            tempCodePoint = (firstByte & 31) << 6 | secondByte & 63;
            if (tempCodePoint > 127) {
              codePoint = tempCodePoint;
            }
          }
          break;
        case 3:
          secondByte = buf[i + 1];
          thirdByte = buf[i + 2];
          if ((secondByte & 192) === 128 && (thirdByte & 192) === 128) {
            tempCodePoint = (firstByte & 15) << 12 | (secondByte & 63) << 6 | thirdByte & 63;
            if (tempCodePoint > 2047 && (tempCodePoint < 55296 || tempCodePoint > 57343)) {
              codePoint = tempCodePoint;
            }
          }
          break;
        case 4:
          secondByte = buf[i + 1];
          thirdByte = buf[i + 2];
          fourthByte = buf[i + 3];
          if ((secondByte & 192) === 128 && (thirdByte & 192) === 128 && (fourthByte & 192) === 128) {
            tempCodePoint = (firstByte & 15) << 18 | (secondByte & 63) << 12 | (thirdByte & 63) << 6 | fourthByte & 63;
            if (tempCodePoint > 65535 && tempCodePoint < 1114112) {
              codePoint = tempCodePoint;
            }
          }
      }
    }
    if (codePoint === null) {
      codePoint = 65533;
      bytesPerSequence = 1;
    } else if (codePoint > 65535) {
      codePoint -= 65536;
      res.push(codePoint >>> 10 & 1023 | 55296);
      codePoint = 56320 | codePoint & 1023;
    }
    res.push(codePoint);
    i += bytesPerSequence;
  }
  return decodeCodePointsArray(res);
}
var MAX_ARGUMENTS_LENGTH = 4096;
function decodeCodePointsArray(codePoints) {
  var len = codePoints.length;
  if (len <= MAX_ARGUMENTS_LENGTH) {
    return String.fromCharCode.apply(String, codePoints);
  }
  var res = "";
  var i = 0;
  while (i < len) {
    res += String.fromCharCode.apply(String, codePoints.slice(i, i += MAX_ARGUMENTS_LENGTH));
  }
  return res;
}
function asciiSlice(buf, start, end) {
  var ret = "";
  end = Math.min(buf.length, end);
  for (var i = start; i < end; ++i) {
    ret += String.fromCharCode(buf[i] & 127);
  }
  return ret;
}
function latin1Slice(buf, start, end) {
  var ret = "";
  end = Math.min(buf.length, end);
  for (var i = start; i < end; ++i) {
    ret += String.fromCharCode(buf[i]);
  }
  return ret;
}
function hexSlice(buf, start, end) {
  var len = buf.length;
  if (!start || start < 0)
    start = 0;
  if (!end || end < 0 || end > len)
    end = len;
  var out = "";
  for (var i = start; i < end; ++i) {
    out += toHex(buf[i]);
  }
  return out;
}
function utf16leSlice(buf, start, end) {
  var bytes = buf.slice(start, end);
  var res = "";
  for (var i = 0; i < bytes.length; i += 2) {
    res += String.fromCharCode(bytes[i] + bytes[i + 1] * 256);
  }
  return res;
}
Buffer.prototype.slice = function slice(start, end) {
  var len = this.length;
  start = ~~start;
  end = end === void 0 ? len : ~~end;
  if (start < 0) {
    start += len;
    if (start < 0)
      start = 0;
  } else if (start > len) {
    start = len;
  }
  if (end < 0) {
    end += len;
    if (end < 0)
      end = 0;
  } else if (end > len) {
    end = len;
  }
  if (end < start)
    end = start;
  var newBuf;
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    newBuf = this.subarray(start, end);
    newBuf.__proto__ = Buffer.prototype;
  } else {
    var sliceLen = end - start;
    newBuf = new Buffer(sliceLen, void 0);
    for (var i = 0; i < sliceLen; ++i) {
      newBuf[i] = this[i + start];
    }
  }
  return newBuf;
};
function checkOffset(offset, ext, length) {
  if (offset % 1 !== 0 || offset < 0)
    throw new RangeError("offset is not uint");
  if (offset + ext > length)
    throw new RangeError("Trying to access beyond buffer length");
}
Buffer.prototype.readUIntLE = function readUIntLE(offset, byteLength2, noAssert) {
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert)
    checkOffset(offset, byteLength2, this.length);
  var val = this[offset];
  var mul = 1;
  var i = 0;
  while (++i < byteLength2 && (mul *= 256)) {
    val += this[offset + i] * mul;
  }
  return val;
};
Buffer.prototype.readUIntBE = function readUIntBE(offset, byteLength2, noAssert) {
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert) {
    checkOffset(offset, byteLength2, this.length);
  }
  var val = this[offset + --byteLength2];
  var mul = 1;
  while (byteLength2 > 0 && (mul *= 256)) {
    val += this[offset + --byteLength2] * mul;
  }
  return val;
};
Buffer.prototype.readUInt8 = function readUInt8(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 1, this.length);
  return this[offset];
};
Buffer.prototype.readUInt16LE = function readUInt16LE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 2, this.length);
  return this[offset] | this[offset + 1] << 8;
};
Buffer.prototype.readUInt16BE = function readUInt16BE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 2, this.length);
  return this[offset] << 8 | this[offset + 1];
};
Buffer.prototype.readUInt32LE = function readUInt32LE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return (this[offset] | this[offset + 1] << 8 | this[offset + 2] << 16) + this[offset + 3] * 16777216;
};
Buffer.prototype.readUInt32BE = function readUInt32BE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return this[offset] * 16777216 + (this[offset + 1] << 16 | this[offset + 2] << 8 | this[offset + 3]);
};
Buffer.prototype.readIntLE = function readIntLE(offset, byteLength2, noAssert) {
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert)
    checkOffset(offset, byteLength2, this.length);
  var val = this[offset];
  var mul = 1;
  var i = 0;
  while (++i < byteLength2 && (mul *= 256)) {
    val += this[offset + i] * mul;
  }
  mul *= 128;
  if (val >= mul)
    val -= Math.pow(2, 8 * byteLength2);
  return val;
};
Buffer.prototype.readIntBE = function readIntBE(offset, byteLength2, noAssert) {
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert)
    checkOffset(offset, byteLength2, this.length);
  var i = byteLength2;
  var mul = 1;
  var val = this[offset + --i];
  while (i > 0 && (mul *= 256)) {
    val += this[offset + --i] * mul;
  }
  mul *= 128;
  if (val >= mul)
    val -= Math.pow(2, 8 * byteLength2);
  return val;
};
Buffer.prototype.readInt8 = function readInt8(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 1, this.length);
  if (!(this[offset] & 128))
    return this[offset];
  return (255 - this[offset] + 1) * -1;
};
Buffer.prototype.readInt16LE = function readInt16LE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 2, this.length);
  var val = this[offset] | this[offset + 1] << 8;
  return val & 32768 ? val | 4294901760 : val;
};
Buffer.prototype.readInt16BE = function readInt16BE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 2, this.length);
  var val = this[offset + 1] | this[offset] << 8;
  return val & 32768 ? val | 4294901760 : val;
};
Buffer.prototype.readInt32LE = function readInt32LE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return this[offset] | this[offset + 1] << 8 | this[offset + 2] << 16 | this[offset + 3] << 24;
};
Buffer.prototype.readInt32BE = function readInt32BE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return this[offset] << 24 | this[offset + 1] << 16 | this[offset + 2] << 8 | this[offset + 3];
};
Buffer.prototype.readFloatLE = function readFloatLE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return read(this, offset, true, 23, 4);
};
Buffer.prototype.readFloatBE = function readFloatBE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return read(this, offset, false, 23, 4);
};
Buffer.prototype.readDoubleLE = function readDoubleLE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 8, this.length);
  return read(this, offset, true, 52, 8);
};
Buffer.prototype.readDoubleBE = function readDoubleBE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 8, this.length);
  return read(this, offset, false, 52, 8);
};
function checkInt(buf, value, offset, ext, max, min) {
  if (!internalIsBuffer(buf))
    throw new TypeError('"buffer" argument must be a Buffer instance');
  if (value > max || value < min)
    throw new RangeError('"value" argument is out of bounds');
  if (offset + ext > buf.length)
    throw new RangeError("Index out of range");
}
Buffer.prototype.writeUIntLE = function writeUIntLE(value, offset, byteLength2, noAssert) {
  value = +value;
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert) {
    var maxBytes = Math.pow(2, 8 * byteLength2) - 1;
    checkInt(this, value, offset, byteLength2, maxBytes, 0);
  }
  var mul = 1;
  var i = 0;
  this[offset] = value & 255;
  while (++i < byteLength2 && (mul *= 256)) {
    this[offset + i] = value / mul & 255;
  }
  return offset + byteLength2;
};
Buffer.prototype.writeUIntBE = function writeUIntBE(value, offset, byteLength2, noAssert) {
  value = +value;
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert) {
    var maxBytes = Math.pow(2, 8 * byteLength2) - 1;
    checkInt(this, value, offset, byteLength2, maxBytes, 0);
  }
  var i = byteLength2 - 1;
  var mul = 1;
  this[offset + i] = value & 255;
  while (--i >= 0 && (mul *= 256)) {
    this[offset + i] = value / mul & 255;
  }
  return offset + byteLength2;
};
Buffer.prototype.writeUInt8 = function writeUInt8(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 1, 255, 0);
  if (!Buffer.TYPED_ARRAY_SUPPORT)
    value = Math.floor(value);
  this[offset] = value & 255;
  return offset + 1;
};
function objectWriteUInt16(buf, value, offset, littleEndian) {
  if (value < 0)
    value = 65535 + value + 1;
  for (var i = 0, j = Math.min(buf.length - offset, 2); i < j; ++i) {
    buf[offset + i] = (value & 255 << 8 * (littleEndian ? i : 1 - i)) >>> (littleEndian ? i : 1 - i) * 8;
  }
}
Buffer.prototype.writeUInt16LE = function writeUInt16LE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 2, 65535, 0);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value & 255;
    this[offset + 1] = value >>> 8;
  } else {
    objectWriteUInt16(this, value, offset, true);
  }
  return offset + 2;
};
Buffer.prototype.writeUInt16BE = function writeUInt16BE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 2, 65535, 0);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value >>> 8;
    this[offset + 1] = value & 255;
  } else {
    objectWriteUInt16(this, value, offset, false);
  }
  return offset + 2;
};
function objectWriteUInt32(buf, value, offset, littleEndian) {
  if (value < 0)
    value = 4294967295 + value + 1;
  for (var i = 0, j = Math.min(buf.length - offset, 4); i < j; ++i) {
    buf[offset + i] = value >>> (littleEndian ? i : 3 - i) * 8 & 255;
  }
}
Buffer.prototype.writeUInt32LE = function writeUInt32LE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 4, 4294967295, 0);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset + 3] = value >>> 24;
    this[offset + 2] = value >>> 16;
    this[offset + 1] = value >>> 8;
    this[offset] = value & 255;
  } else {
    objectWriteUInt32(this, value, offset, true);
  }
  return offset + 4;
};
Buffer.prototype.writeUInt32BE = function writeUInt32BE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 4, 4294967295, 0);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value >>> 24;
    this[offset + 1] = value >>> 16;
    this[offset + 2] = value >>> 8;
    this[offset + 3] = value & 255;
  } else {
    objectWriteUInt32(this, value, offset, false);
  }
  return offset + 4;
};
Buffer.prototype.writeIntLE = function writeIntLE(value, offset, byteLength2, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert) {
    var limit = Math.pow(2, 8 * byteLength2 - 1);
    checkInt(this, value, offset, byteLength2, limit - 1, -limit);
  }
  var i = 0;
  var mul = 1;
  var sub = 0;
  this[offset] = value & 255;
  while (++i < byteLength2 && (mul *= 256)) {
    if (value < 0 && sub === 0 && this[offset + i - 1] !== 0) {
      sub = 1;
    }
    this[offset + i] = (value / mul >> 0) - sub & 255;
  }
  return offset + byteLength2;
};
Buffer.prototype.writeIntBE = function writeIntBE(value, offset, byteLength2, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert) {
    var limit = Math.pow(2, 8 * byteLength2 - 1);
    checkInt(this, value, offset, byteLength2, limit - 1, -limit);
  }
  var i = byteLength2 - 1;
  var mul = 1;
  var sub = 0;
  this[offset + i] = value & 255;
  while (--i >= 0 && (mul *= 256)) {
    if (value < 0 && sub === 0 && this[offset + i + 1] !== 0) {
      sub = 1;
    }
    this[offset + i] = (value / mul >> 0) - sub & 255;
  }
  return offset + byteLength2;
};
Buffer.prototype.writeInt8 = function writeInt8(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 1, 127, -128);
  if (!Buffer.TYPED_ARRAY_SUPPORT)
    value = Math.floor(value);
  if (value < 0)
    value = 255 + value + 1;
  this[offset] = value & 255;
  return offset + 1;
};
Buffer.prototype.writeInt16LE = function writeInt16LE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 2, 32767, -32768);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value & 255;
    this[offset + 1] = value >>> 8;
  } else {
    objectWriteUInt16(this, value, offset, true);
  }
  return offset + 2;
};
Buffer.prototype.writeInt16BE = function writeInt16BE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 2, 32767, -32768);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value >>> 8;
    this[offset + 1] = value & 255;
  } else {
    objectWriteUInt16(this, value, offset, false);
  }
  return offset + 2;
};
Buffer.prototype.writeInt32LE = function writeInt32LE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 4, 2147483647, -2147483648);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value & 255;
    this[offset + 1] = value >>> 8;
    this[offset + 2] = value >>> 16;
    this[offset + 3] = value >>> 24;
  } else {
    objectWriteUInt32(this, value, offset, true);
  }
  return offset + 4;
};
Buffer.prototype.writeInt32BE = function writeInt32BE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 4, 2147483647, -2147483648);
  if (value < 0)
    value = 4294967295 + value + 1;
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value >>> 24;
    this[offset + 1] = value >>> 16;
    this[offset + 2] = value >>> 8;
    this[offset + 3] = value & 255;
  } else {
    objectWriteUInt32(this, value, offset, false);
  }
  return offset + 4;
};
function checkIEEE754(buf, value, offset, ext, max, min) {
  if (offset + ext > buf.length)
    throw new RangeError("Index out of range");
  if (offset < 0)
    throw new RangeError("Index out of range");
}
function writeFloat(buf, value, offset, littleEndian, noAssert) {
  if (!noAssert) {
    checkIEEE754(buf, value, offset, 4);
  }
  write(buf, value, offset, littleEndian, 23, 4);
  return offset + 4;
}
Buffer.prototype.writeFloatLE = function writeFloatLE(value, offset, noAssert) {
  return writeFloat(this, value, offset, true, noAssert);
};
Buffer.prototype.writeFloatBE = function writeFloatBE(value, offset, noAssert) {
  return writeFloat(this, value, offset, false, noAssert);
};
function writeDouble(buf, value, offset, littleEndian, noAssert) {
  if (!noAssert) {
    checkIEEE754(buf, value, offset, 8);
  }
  write(buf, value, offset, littleEndian, 52, 8);
  return offset + 8;
}
Buffer.prototype.writeDoubleLE = function writeDoubleLE(value, offset, noAssert) {
  return writeDouble(this, value, offset, true, noAssert);
};
Buffer.prototype.writeDoubleBE = function writeDoubleBE(value, offset, noAssert) {
  return writeDouble(this, value, offset, false, noAssert);
};
Buffer.prototype.copy = function copy(target, targetStart, start, end) {
  if (!start)
    start = 0;
  if (!end && end !== 0)
    end = this.length;
  if (targetStart >= target.length)
    targetStart = target.length;
  if (!targetStart)
    targetStart = 0;
  if (end > 0 && end < start)
    end = start;
  if (end === start)
    return 0;
  if (target.length === 0 || this.length === 0)
    return 0;
  if (targetStart < 0) {
    throw new RangeError("targetStart out of bounds");
  }
  if (start < 0 || start >= this.length)
    throw new RangeError("sourceStart out of bounds");
  if (end < 0)
    throw new RangeError("sourceEnd out of bounds");
  if (end > this.length)
    end = this.length;
  if (target.length - targetStart < end - start) {
    end = target.length - targetStart + start;
  }
  var len = end - start;
  var i;
  if (this === target && start < targetStart && targetStart < end) {
    for (i = len - 1; i >= 0; --i) {
      target[i + targetStart] = this[i + start];
    }
  } else if (len < 1e3 || !Buffer.TYPED_ARRAY_SUPPORT) {
    for (i = 0; i < len; ++i) {
      target[i + targetStart] = this[i + start];
    }
  } else {
    Uint8Array.prototype.set.call(target, this.subarray(start, start + len), targetStart);
  }
  return len;
};
Buffer.prototype.fill = function fill(val, start, end, encoding) {
  if (typeof val === "string") {
    if (typeof start === "string") {
      encoding = start;
      start = 0;
      end = this.length;
    } else if (typeof end === "string") {
      encoding = end;
      end = this.length;
    }
    if (val.length === 1) {
      var code = val.charCodeAt(0);
      if (code < 256) {
        val = code;
      }
    }
    if (encoding !== void 0 && typeof encoding !== "string") {
      throw new TypeError("encoding must be a string");
    }
    if (typeof encoding === "string" && !Buffer.isEncoding(encoding)) {
      throw new TypeError("Unknown encoding: " + encoding);
    }
  } else if (typeof val === "number") {
    val = val & 255;
  }
  if (start < 0 || this.length < start || this.length < end) {
    throw new RangeError("Out of range index");
  }
  if (end <= start) {
    return this;
  }
  start = start >>> 0;
  end = end === void 0 ? this.length : end >>> 0;
  if (!val)
    val = 0;
  var i;
  if (typeof val === "number") {
    for (i = start; i < end; ++i) {
      this[i] = val;
    }
  } else {
    var bytes = internalIsBuffer(val) ? val : utf8ToBytes(new Buffer(val, encoding).toString());
    var len = bytes.length;
    for (i = 0; i < end - start; ++i) {
      this[i + start] = bytes[i % len];
    }
  }
  return this;
};
var INVALID_BASE64_RE = /[^+\/0-9A-Za-z-_]/g;
function base64clean(str) {
  str = stringtrim(str).replace(INVALID_BASE64_RE, "");
  if (str.length < 2)
    return "";
  while (str.length % 4 !== 0) {
    str = str + "=";
  }
  return str;
}
function stringtrim(str) {
  if (str.trim)
    return str.trim();
  return str.replace(/^\s+|\s+$/g, "");
}
function toHex(n) {
  if (n < 16)
    return "0" + n.toString(16);
  return n.toString(16);
}
function utf8ToBytes(string, units) {
  units = units || Infinity;
  var codePoint;
  var length = string.length;
  var leadSurrogate = null;
  var bytes = [];
  for (var i = 0; i < length; ++i) {
    codePoint = string.charCodeAt(i);
    if (codePoint > 55295 && codePoint < 57344) {
      if (!leadSurrogate) {
        if (codePoint > 56319) {
          if ((units -= 3) > -1)
            bytes.push(239, 191, 189);
          continue;
        } else if (i + 1 === length) {
          if ((units -= 3) > -1)
            bytes.push(239, 191, 189);
          continue;
        }
        leadSurrogate = codePoint;
        continue;
      }
      if (codePoint < 56320) {
        if ((units -= 3) > -1)
          bytes.push(239, 191, 189);
        leadSurrogate = codePoint;
        continue;
      }
      codePoint = (leadSurrogate - 55296 << 10 | codePoint - 56320) + 65536;
    } else if (leadSurrogate) {
      if ((units -= 3) > -1)
        bytes.push(239, 191, 189);
    }
    leadSurrogate = null;
    if (codePoint < 128) {
      if ((units -= 1) < 0)
        break;
      bytes.push(codePoint);
    } else if (codePoint < 2048) {
      if ((units -= 2) < 0)
        break;
      bytes.push(codePoint >> 6 | 192, codePoint & 63 | 128);
    } else if (codePoint < 65536) {
      if ((units -= 3) < 0)
        break;
      bytes.push(codePoint >> 12 | 224, codePoint >> 6 & 63 | 128, codePoint & 63 | 128);
    } else if (codePoint < 1114112) {
      if ((units -= 4) < 0)
        break;
      bytes.push(codePoint >> 18 | 240, codePoint >> 12 & 63 | 128, codePoint >> 6 & 63 | 128, codePoint & 63 | 128);
    } else {
      throw new Error("Invalid code point");
    }
  }
  return bytes;
}
function asciiToBytes(str) {
  var byteArray = [];
  for (var i = 0; i < str.length; ++i) {
    byteArray.push(str.charCodeAt(i) & 255);
  }
  return byteArray;
}
function utf16leToBytes(str, units) {
  var c, hi, lo;
  var byteArray = [];
  for (var i = 0; i < str.length; ++i) {
    if ((units -= 2) < 0)
      break;
    c = str.charCodeAt(i);
    hi = c >> 8;
    lo = c % 256;
    byteArray.push(lo);
    byteArray.push(hi);
  }
  return byteArray;
}
function base64ToBytes(str) {
  return toByteArray(base64clean(str));
}
function blitBuffer(src, dst, offset, length) {
  for (var i = 0; i < length; ++i) {
    if (i + offset >= dst.length || i >= src.length)
      break;
    dst[i + offset] = src[i];
  }
  return i;
}
function isnan(val) {
  return val !== val;
}
function isBuffer$1(obj) {
  return obj != null && (!!obj._isBuffer || isFastBuffer(obj) || isSlowBuffer(obj));
}
function isFastBuffer(obj) {
  return !!obj.constructor && typeof obj.constructor.isBuffer === "function" && obj.constructor.isBuffer(obj);
}
function isSlowBuffer(obj) {
  return typeof obj.readFloatLE === "function" && typeof obj.slice === "function" && isFastBuffer(obj.slice(0, 0));
}
function AxiosError(message, code, config, request, response) {
  Error.call(this);
  if (Error.captureStackTrace) {
    Error.captureStackTrace(this, this.constructor);
  } else {
    this.stack = new Error().stack;
  }
  this.message = message;
  this.name = "AxiosError";
  code && (this.code = code);
  config && (this.config = config);
  request && (this.request = request);
  response && (this.response = response);
}
utils.inherits(AxiosError, Error, {
  toJSON: function toJSON2() {
    return {
      message: this.message,
      name: this.name,
      description: this.description,
      number: this.number,
      fileName: this.fileName,
      lineNumber: this.lineNumber,
      columnNumber: this.columnNumber,
      stack: this.stack,
      config: utils.toJSONObject(this.config),
      code: this.code,
      status: this.response && this.response.status ? this.response.status : null
    };
  }
});
const prototype = AxiosError.prototype;
const descriptors = {};
[
  "ERR_BAD_OPTION_VALUE",
  "ERR_BAD_OPTION",
  "ECONNABORTED",
  "ETIMEDOUT",
  "ERR_NETWORK",
  "ERR_FR_TOO_MANY_REDIRECTS",
  "ERR_DEPRECATED",
  "ERR_BAD_RESPONSE",
  "ERR_BAD_REQUEST",
  "ERR_CANCELED",
  "ERR_NOT_SUPPORT",
  "ERR_INVALID_URL"
].forEach((code) => {
  descriptors[code] = {value: code};
});
Object.defineProperties(AxiosError, descriptors);
Object.defineProperty(prototype, "isAxiosError", {value: true});
AxiosError.from = (error, code, config, request, response, customProps) => {
  const axiosError = Object.create(prototype);
  utils.toFlatObject(error, axiosError, function filter2(obj) {
    return obj !== Error.prototype;
  }, (prop) => {
    return prop !== "isAxiosError";
  });
  AxiosError.call(axiosError, error.message, code, config, request, response);
  axiosError.cause = error;
  axiosError.name = error.name;
  customProps && Object.assign(axiosError, customProps);
  return axiosError;
};
function isVisitable(thing) {
  return utils.isPlainObject(thing) || utils.isArray(thing);
}
function removeBrackets(key) {
  return utils.endsWith(key, "[]") ? key.slice(0, -2) : key;
}
function renderKey(path, key, dots) {
  if (!path)
    return key;
  return path.concat(key).map(function each(token, i) {
    token = removeBrackets(token);
    return !dots && i ? "[" + token + "]" : token;
  }).join(dots ? "." : "");
}
function isFlatArray(arr) {
  return utils.isArray(arr) && !arr.some(isVisitable);
}
const predicates = utils.toFlatObject(utils, {}, null, function filter(prop) {
  return /^is[A-Z]/.test(prop);
});
function isSpecCompliant(thing) {
  return thing && utils.isFunction(thing.append) && thing[Symbol.toStringTag] === "FormData" && thing[Symbol.iterator];
}
function toFormData(obj, formData, options) {
  if (!utils.isObject(obj)) {
    throw new TypeError("target must be an object");
  }
  formData = formData || new (browser || FormData)();
  options = utils.toFlatObject(options, {
    metaTokens: true,
    dots: false,
    indexes: false
  }, false, function defined(option, source) {
    return !utils.isUndefined(source[option]);
  });
  const metaTokens = options.metaTokens;
  const visitor = options.visitor || defaultVisitor;
  const dots = options.dots;
  const indexes = options.indexes;
  const _Blob = options.Blob || typeof Blob !== "undefined" && Blob;
  const useBlob = _Blob && isSpecCompliant(formData);
  if (!utils.isFunction(visitor)) {
    throw new TypeError("visitor must be a function");
  }
  function convertValue(value) {
    if (value === null)
      return "";
    if (utils.isDate(value)) {
      return value.toISOString();
    }
    if (!useBlob && utils.isBlob(value)) {
      throw new AxiosError("Blob is not supported. Use a Buffer instead.");
    }
    if (utils.isArrayBuffer(value) || utils.isTypedArray(value)) {
      return useBlob && typeof Blob === "function" ? new Blob([value]) : Buffer.from(value);
    }
    return value;
  }
  function defaultVisitor(value, key, path) {
    let arr = value;
    if (value && !path && typeof value === "object") {
      if (utils.endsWith(key, "{}")) {
        key = metaTokens ? key : key.slice(0, -2);
        value = JSON.stringify(value);
      } else if (utils.isArray(value) && isFlatArray(value) || (utils.isFileList(value) || utils.endsWith(key, "[]") && (arr = utils.toArray(value)))) {
        key = removeBrackets(key);
        arr.forEach(function each(el, index) {
          !(utils.isUndefined(el) || el === null) && formData.append(indexes === true ? renderKey([key], index, dots) : indexes === null ? key : key + "[]", convertValue(el));
        });
        return false;
      }
    }
    if (isVisitable(value)) {
      return true;
    }
    formData.append(renderKey(path, key, dots), convertValue(value));
    return false;
  }
  const stack = [];
  const exposedHelpers = Object.assign(predicates, {
    defaultVisitor,
    convertValue,
    isVisitable
  });
  function build(value, path) {
    if (utils.isUndefined(value))
      return;
    if (stack.indexOf(value) !== -1) {
      throw Error("Circular reference detected in " + path.join("."));
    }
    stack.push(value);
    utils.forEach(value, function each(el, key) {
      const result = !(utils.isUndefined(el) || el === null) && visitor.call(formData, el, utils.isString(key) ? key.trim() : key, path, exposedHelpers);
      if (result === true) {
        build(el, path ? path.concat(key) : [key]);
      }
    });
    stack.pop();
  }
  if (!utils.isObject(obj)) {
    throw new TypeError("data must be an object");
  }
  build(obj);
  return formData;
}
function encode(str) {
  const charMap = {
    "!": "%21",
    "'": "%27",
    "(": "%28",
    ")": "%29",
    "~": "%7E",
    "%20": "+",
    "%00": "\0"
  };
  return encodeURIComponent(str).replace(/[!'()~]|%20|%00/g, function replacer(match) {
    return charMap[match];
  });
}
function AxiosURLSearchParams(params, options) {
  this._pairs = [];
  params && toFormData(params, this, options);
}
const prototype$1 = AxiosURLSearchParams.prototype;
prototype$1.append = function append(name, value) {
  this._pairs.push([name, value]);
};
prototype$1.toString = function toString3(encoder) {
  const _encode = encoder ? function(value) {
    return encoder.call(this, value, encode);
  } : encode;
  return this._pairs.map(function each(pair) {
    return _encode(pair[0]) + "=" + _encode(pair[1]);
  }, "").join("&");
};
function encode$1(val) {
  return encodeURIComponent(val).replace(/%3A/gi, ":").replace(/%24/g, "$").replace(/%2C/gi, ",").replace(/%20/g, "+").replace(/%5B/gi, "[").replace(/%5D/gi, "]");
}
function buildURL(url, params, options) {
  if (!params) {
    return url;
  }
  const _encode = options && options.encode || encode$1;
  const serializeFn = options && options.serialize;
  let serializedParams;
  if (serializeFn) {
    serializedParams = serializeFn(params, options);
  } else {
    serializedParams = utils.isURLSearchParams(params) ? params.toString() : new AxiosURLSearchParams(params, options).toString(_encode);
  }
  if (serializedParams) {
    const hashmarkIndex = url.indexOf("#");
    if (hashmarkIndex !== -1) {
      url = url.slice(0, hashmarkIndex);
    }
    url += (url.indexOf("?") === -1 ? "?" : "&") + serializedParams;
  }
  return url;
}
class InterceptorManager {
  constructor() {
    this.handlers = [];
  }
  use(fulfilled, rejected, options) {
    this.handlers.push({
      fulfilled,
      rejected,
      synchronous: options ? options.synchronous : false,
      runWhen: options ? options.runWhen : null
    });
    return this.handlers.length - 1;
  }
  eject(id) {
    if (this.handlers[id]) {
      this.handlers[id] = null;
    }
  }
  clear() {
    if (this.handlers) {
      this.handlers = [];
    }
  }
  forEach(fn) {
    utils.forEach(this.handlers, function forEachHandler(h) {
      if (h !== null) {
        fn(h);
      }
    });
  }
}
var transitionalDefaults = {
  silentJSONParsing: true,
  forcedJSONParsing: true,
  clarifyTimeoutError: false
};
var URLSearchParams$1 = typeof URLSearchParams !== "undefined" ? URLSearchParams : AxiosURLSearchParams;
var FormData$1 = FormData;
const isStandardBrowserEnv = (() => {
  let product;
  if (typeof navigator !== "undefined" && ((product = navigator.product) === "ReactNative" || product === "NativeScript" || product === "NS")) {
    return false;
  }
  return typeof window !== "undefined" && typeof document !== "undefined";
})();
var platform = {
  isBrowser: true,
  classes: {
    URLSearchParams: URLSearchParams$1,
    FormData: FormData$1,
    Blob
  },
  isStandardBrowserEnv,
  protocols: ["http", "https", "file", "blob", "url", "data"]
};
function toURLEncodedForm(data, options) {
  return toFormData(data, new platform.classes.URLSearchParams(), Object.assign({
    visitor: function(value, key, path, helpers) {
      return helpers.defaultVisitor.apply(this, arguments);
    }
  }, options));
}
function parsePropPath(name) {
  return utils.matchAll(/\w+|\[(\w*)]/g, name).map((match) => {
    return match[0] === "[]" ? "" : match[1] || match[0];
  });
}
function arrayToObject(arr) {
  const obj = {};
  const keys = Object.keys(arr);
  let i;
  const len = keys.length;
  let key;
  for (i = 0; i < len; i++) {
    key = keys[i];
    obj[key] = arr[key];
  }
  return obj;
}
function formDataToJSON(formData) {
  function buildPath(path, value, target, index) {
    let name = path[index++];
    const isNumericKey = Number.isFinite(+name);
    const isLast = index >= path.length;
    name = !name && utils.isArray(target) ? target.length : name;
    if (isLast) {
      if (utils.hasOwnProp(target, name)) {
        target[name] = [target[name], value];
      } else {
        target[name] = value;
      }
      return !isNumericKey;
    }
    if (!target[name] || !utils.isObject(target[name])) {
      target[name] = [];
    }
    const result = buildPath(path, value, target[name], index);
    if (result && utils.isArray(target[name])) {
      target[name] = arrayToObject(target[name]);
    }
    return !isNumericKey;
  }
  if (utils.isFormData(formData) && utils.isFunction(formData.entries)) {
    const obj = {};
    utils.forEachEntry(formData, (name, value) => {
      buildPath(parsePropPath(name), value, obj, 0);
    });
    return obj;
  }
  return null;
}
const DEFAULT_CONTENT_TYPE = {
  "Content-Type": void 0
};
function stringifySafely(rawValue, parser, encoder) {
  if (utils.isString(rawValue)) {
    try {
      (parser || JSON.parse)(rawValue);
      return utils.trim(rawValue);
    } catch (e) {
      if (e.name !== "SyntaxError") {
        throw e;
      }
    }
  }
  return (encoder || JSON.stringify)(rawValue);
}
const defaults = {
  transitional: transitionalDefaults,
  adapter: ["xhr", "http"],
  transformRequest: [function transformRequest(data, headers) {
    const contentType = headers.getContentType() || "";
    const hasJSONContentType = contentType.indexOf("application/json") > -1;
    const isObjectPayload = utils.isObject(data);
    if (isObjectPayload && utils.isHTMLForm(data)) {
      data = new FormData(data);
    }
    const isFormData2 = utils.isFormData(data);
    if (isFormData2) {
      if (!hasJSONContentType) {
        return data;
      }
      return hasJSONContentType ? JSON.stringify(formDataToJSON(data)) : data;
    }
    if (utils.isArrayBuffer(data) || utils.isBuffer(data) || utils.isStream(data) || utils.isFile(data) || utils.isBlob(data)) {
      return data;
    }
    if (utils.isArrayBufferView(data)) {
      return data.buffer;
    }
    if (utils.isURLSearchParams(data)) {
      headers.setContentType("application/x-www-form-urlencoded;charset=utf-8", false);
      return data.toString();
    }
    let isFileList2;
    if (isObjectPayload) {
      if (contentType.indexOf("application/x-www-form-urlencoded") > -1) {
        return toURLEncodedForm(data, this.formSerializer).toString();
      }
      if ((isFileList2 = utils.isFileList(data)) || contentType.indexOf("multipart/form-data") > -1) {
        const _FormData = this.env && this.env.FormData;
        return toFormData(isFileList2 ? {"files[]": data} : data, _FormData && new _FormData(), this.formSerializer);
      }
    }
    if (isObjectPayload || hasJSONContentType) {
      headers.setContentType("application/json", false);
      return stringifySafely(data);
    }
    return data;
  }],
  transformResponse: [function transformResponse(data) {
    const transitional2 = this.transitional || defaults.transitional;
    const forcedJSONParsing = transitional2 && transitional2.forcedJSONParsing;
    const JSONRequested = this.responseType === "json";
    if (data && utils.isString(data) && (forcedJSONParsing && !this.responseType || JSONRequested)) {
      const silentJSONParsing = transitional2 && transitional2.silentJSONParsing;
      const strictJSONParsing = !silentJSONParsing && JSONRequested;
      try {
        return JSON.parse(data);
      } catch (e) {
        if (strictJSONParsing) {
          if (e.name === "SyntaxError") {
            throw AxiosError.from(e, AxiosError.ERR_BAD_RESPONSE, this, null, this.response);
          }
          throw e;
        }
      }
    }
    return data;
  }],
  timeout: 0,
  xsrfCookieName: "XSRF-TOKEN",
  xsrfHeaderName: "X-XSRF-TOKEN",
  maxContentLength: -1,
  maxBodyLength: -1,
  env: {
    FormData: platform.classes.FormData,
    Blob: platform.classes.Blob
  },
  validateStatus: function validateStatus(status) {
    return status >= 200 && status < 300;
  },
  headers: {
    common: {
      Accept: "application/json, text/plain, */*"
    }
  }
};
utils.forEach(["delete", "get", "head"], function forEachMethodNoData(method) {
  defaults.headers[method] = {};
});
utils.forEach(["post", "put", "patch"], function forEachMethodWithData(method) {
  defaults.headers[method] = utils.merge(DEFAULT_CONTENT_TYPE);
});
const ignoreDuplicateOf = utils.toObjectSet([
  "age",
  "authorization",
  "content-length",
  "content-type",
  "etag",
  "expires",
  "from",
  "host",
  "if-modified-since",
  "if-unmodified-since",
  "last-modified",
  "location",
  "max-forwards",
  "proxy-authorization",
  "referer",
  "retry-after",
  "user-agent"
]);
var parseHeaders = (rawHeaders) => {
  const parsed = {};
  let key;
  let val;
  let i;
  rawHeaders && rawHeaders.split("\n").forEach(function parser(line) {
    i = line.indexOf(":");
    key = line.substring(0, i).trim().toLowerCase();
    val = line.substring(i + 1).trim();
    if (!key || parsed[key] && ignoreDuplicateOf[key]) {
      return;
    }
    if (key === "set-cookie") {
      if (parsed[key]) {
        parsed[key].push(val);
      } else {
        parsed[key] = [val];
      }
    } else {
      parsed[key] = parsed[key] ? parsed[key] + ", " + val : val;
    }
  });
  return parsed;
};
const $internals = Symbol("internals");
function normalizeHeader(header) {
  return header && String(header).trim().toLowerCase();
}
function normalizeValue(value) {
  if (value === false || value == null) {
    return value;
  }
  return utils.isArray(value) ? value.map(normalizeValue) : String(value);
}
function parseTokens(str) {
  const tokens = Object.create(null);
  const tokensRE = /([^\s,;=]+)\s*(?:=\s*([^,;]+))?/g;
  let match;
  while (match = tokensRE.exec(str)) {
    tokens[match[1]] = match[2];
  }
  return tokens;
}
function isValidHeaderName(str) {
  return /^[-_a-zA-Z]+$/.test(str.trim());
}
function matchHeaderValue(context, value, header, filter2) {
  if (utils.isFunction(filter2)) {
    return filter2.call(this, value, header);
  }
  if (!utils.isString(value))
    return;
  if (utils.isString(filter2)) {
    return value.indexOf(filter2) !== -1;
  }
  if (utils.isRegExp(filter2)) {
    return filter2.test(value);
  }
}
function formatHeader(header) {
  return header.trim().toLowerCase().replace(/([a-z\d])(\w*)/g, (w, char, str) => {
    return char.toUpperCase() + str;
  });
}
function buildAccessors(obj, header) {
  const accessorName = utils.toCamelCase(" " + header);
  ["get", "set", "has"].forEach((methodName) => {
    Object.defineProperty(obj, methodName + accessorName, {
      value: function(arg1, arg2, arg3) {
        return this[methodName].call(this, header, arg1, arg2, arg3);
      },
      configurable: true
    });
  });
}
class AxiosHeaders {
  constructor(headers) {
    headers && this.set(headers);
  }
  set(header, valueOrRewrite, rewrite) {
    const self2 = this;
    function setHeader(_value, _header, _rewrite) {
      const lHeader = normalizeHeader(_header);
      if (!lHeader) {
        throw new Error("header name must be a non-empty string");
      }
      const key = utils.findKey(self2, lHeader);
      if (!key || self2[key] === void 0 || _rewrite === true || _rewrite === void 0 && self2[key] !== false) {
        self2[key || _header] = normalizeValue(_value);
      }
    }
    const setHeaders = (headers, _rewrite) => utils.forEach(headers, (_value, _header) => setHeader(_value, _header, _rewrite));
    if (utils.isPlainObject(header) || header instanceof this.constructor) {
      setHeaders(header, valueOrRewrite);
    } else if (utils.isString(header) && (header = header.trim()) && !isValidHeaderName(header)) {
      setHeaders(parseHeaders(header), valueOrRewrite);
    } else {
      header != null && setHeader(valueOrRewrite, header, rewrite);
    }
    return this;
  }
  get(header, parser) {
    header = normalizeHeader(header);
    if (header) {
      const key = utils.findKey(this, header);
      if (key) {
        const value = this[key];
        if (!parser) {
          return value;
        }
        if (parser === true) {
          return parseTokens(value);
        }
        if (utils.isFunction(parser)) {
          return parser.call(this, value, key);
        }
        if (utils.isRegExp(parser)) {
          return parser.exec(value);
        }
        throw new TypeError("parser must be boolean|regexp|function");
      }
    }
  }
  has(header, matcher) {
    header = normalizeHeader(header);
    if (header) {
      const key = utils.findKey(this, header);
      return !!(key && (!matcher || matchHeaderValue(this, this[key], key, matcher)));
    }
    return false;
  }
  delete(header, matcher) {
    const self2 = this;
    let deleted = false;
    function deleteHeader(_header) {
      _header = normalizeHeader(_header);
      if (_header) {
        const key = utils.findKey(self2, _header);
        if (key && (!matcher || matchHeaderValue(self2, self2[key], key, matcher))) {
          delete self2[key];
          deleted = true;
        }
      }
    }
    if (utils.isArray(header)) {
      header.forEach(deleteHeader);
    } else {
      deleteHeader(header);
    }
    return deleted;
  }
  clear() {
    return Object.keys(this).forEach(this.delete.bind(this));
  }
  normalize(format) {
    const self2 = this;
    const headers = {};
    utils.forEach(this, (value, header) => {
      const key = utils.findKey(headers, header);
      if (key) {
        self2[key] = normalizeValue(value);
        delete self2[header];
        return;
      }
      const normalized = format ? formatHeader(header) : String(header).trim();
      if (normalized !== header) {
        delete self2[header];
      }
      self2[normalized] = normalizeValue(value);
      headers[normalized] = true;
    });
    return this;
  }
  concat(...targets) {
    return this.constructor.concat(this, ...targets);
  }
  toJSON(asStrings) {
    const obj = Object.create(null);
    utils.forEach(this, (value, header) => {
      value != null && value !== false && (obj[header] = asStrings && utils.isArray(value) ? value.join(", ") : value);
    });
    return obj;
  }
  [Symbol.iterator]() {
    return Object.entries(this.toJSON())[Symbol.iterator]();
  }
  toString() {
    return Object.entries(this.toJSON()).map(([header, value]) => header + ": " + value).join("\n");
  }
  get [Symbol.toStringTag]() {
    return "AxiosHeaders";
  }
  static from(thing) {
    return thing instanceof this ? thing : new this(thing);
  }
  static concat(first, ...targets) {
    const computed = new this(first);
    targets.forEach((target) => computed.set(target));
    return computed;
  }
  static accessor(header) {
    const internals = this[$internals] = this[$internals] = {
      accessors: {}
    };
    const accessors = internals.accessors;
    const prototype2 = this.prototype;
    function defineAccessor(_header) {
      const lHeader = normalizeHeader(_header);
      if (!accessors[lHeader]) {
        buildAccessors(prototype2, _header);
        accessors[lHeader] = true;
      }
    }
    utils.isArray(header) ? header.forEach(defineAccessor) : defineAccessor(header);
    return this;
  }
}
AxiosHeaders.accessor(["Content-Type", "Content-Length", "Accept", "Accept-Encoding", "User-Agent"]);
utils.freezeMethods(AxiosHeaders.prototype);
utils.freezeMethods(AxiosHeaders);
function transformData(fns, response) {
  const config = this || defaults;
  const context = response || config;
  const headers = AxiosHeaders.from(context.headers);
  let data = context.data;
  utils.forEach(fns, function transform(fn) {
    data = fn.call(config, data, headers.normalize(), response ? response.status : void 0);
  });
  headers.normalize();
  return data;
}
function isCancel(value) {
  return !!(value && value.__CANCEL__);
}
function CanceledError(message, config, request) {
  AxiosError.call(this, message == null ? "canceled" : message, AxiosError.ERR_CANCELED, config, request);
  this.name = "CanceledError";
}
utils.inherits(CanceledError, AxiosError, {
  __CANCEL__: true
});
var httpAdapter = null;
function settle(resolve, reject, response) {
  const validateStatus2 = response.config.validateStatus;
  if (!response.status || !validateStatus2 || validateStatus2(response.status)) {
    resolve(response);
  } else {
    reject(new AxiosError("Request failed with status code " + response.status, [AxiosError.ERR_BAD_REQUEST, AxiosError.ERR_BAD_RESPONSE][Math.floor(response.status / 100) - 4], response.config, response.request, response));
  }
}
var cookies = platform.isStandardBrowserEnv ? function standardBrowserEnv() {
  return {
    write: function write3(name, value, expires, path, domain, secure) {
      const cookie = [];
      cookie.push(name + "=" + encodeURIComponent(value));
      if (utils.isNumber(expires)) {
        cookie.push("expires=" + new Date(expires).toGMTString());
      }
      if (utils.isString(path)) {
        cookie.push("path=" + path);
      }
      if (utils.isString(domain)) {
        cookie.push("domain=" + domain);
      }
      if (secure === true) {
        cookie.push("secure");
      }
      document.cookie = cookie.join("; ");
    },
    read: function read2(name) {
      const match = document.cookie.match(new RegExp("(^|;\\s*)(" + name + ")=([^;]*)"));
      return match ? decodeURIComponent(match[3]) : null;
    },
    remove: function remove(name) {
      this.write(name, "", Date.now() - 864e5);
    }
  };
}() : function nonStandardBrowserEnv() {
  return {
    write: function write3() {
    },
    read: function read2() {
      return null;
    },
    remove: function remove() {
    }
  };
}();
function isAbsoluteURL(url) {
  return /^([a-z][a-z\d+\-.]*:)?\/\//i.test(url);
}
function combineURLs(baseURL, relativeURL) {
  return relativeURL ? baseURL.replace(/\/+$/, "") + "/" + relativeURL.replace(/^\/+/, "") : baseURL;
}
function buildFullPath(baseURL, requestedURL) {
  if (baseURL && !isAbsoluteURL(requestedURL)) {
    return combineURLs(baseURL, requestedURL);
  }
  return requestedURL;
}
var isURLSameOrigin = platform.isStandardBrowserEnv ? function standardBrowserEnv2() {
  const msie = /(msie|trident)/i.test(navigator.userAgent);
  const urlParsingNode = document.createElement("a");
  let originURL;
  function resolveURL(url) {
    let href = url;
    if (msie) {
      urlParsingNode.setAttribute("href", href);
      href = urlParsingNode.href;
    }
    urlParsingNode.setAttribute("href", href);
    return {
      href: urlParsingNode.href,
      protocol: urlParsingNode.protocol ? urlParsingNode.protocol.replace(/:$/, "") : "",
      host: urlParsingNode.host,
      search: urlParsingNode.search ? urlParsingNode.search.replace(/^\?/, "") : "",
      hash: urlParsingNode.hash ? urlParsingNode.hash.replace(/^#/, "") : "",
      hostname: urlParsingNode.hostname,
      port: urlParsingNode.port,
      pathname: urlParsingNode.pathname.charAt(0) === "/" ? urlParsingNode.pathname : "/" + urlParsingNode.pathname
    };
  }
  originURL = resolveURL(window.location.href);
  return function isURLSameOrigin2(requestURL) {
    const parsed = utils.isString(requestURL) ? resolveURL(requestURL) : requestURL;
    return parsed.protocol === originURL.protocol && parsed.host === originURL.host;
  };
}() : function nonStandardBrowserEnv2() {
  return function isURLSameOrigin2() {
    return true;
  };
}();
function parseProtocol(url) {
  const match = /^([-+\w]{1,25})(:?\/\/|:)/.exec(url);
  return match && match[1] || "";
}
function speedometer(samplesCount, min) {
  samplesCount = samplesCount || 10;
  const bytes = new Array(samplesCount);
  const timestamps = new Array(samplesCount);
  let head = 0;
  let tail = 0;
  let firstSampleTS;
  min = min !== void 0 ? min : 1e3;
  return function push(chunkLength) {
    const now = Date.now();
    const startedAt = timestamps[tail];
    if (!firstSampleTS) {
      firstSampleTS = now;
    }
    bytes[head] = chunkLength;
    timestamps[head] = now;
    let i = tail;
    let bytesCount = 0;
    while (i !== head) {
      bytesCount += bytes[i++];
      i = i % samplesCount;
    }
    head = (head + 1) % samplesCount;
    if (head === tail) {
      tail = (tail + 1) % samplesCount;
    }
    if (now - firstSampleTS < min) {
      return;
    }
    const passed = startedAt && now - startedAt;
    return passed ? Math.round(bytesCount * 1e3 / passed) : void 0;
  };
}
function progressEventReducer(listener, isDownloadStream) {
  let bytesNotified = 0;
  const _speedometer = speedometer(50, 250);
  return (e) => {
    const loaded = e.loaded;
    const total = e.lengthComputable ? e.total : void 0;
    const progressBytes = loaded - bytesNotified;
    const rate = _speedometer(progressBytes);
    const inRange = loaded <= total;
    bytesNotified = loaded;
    const data = {
      loaded,
      total,
      progress: total ? loaded / total : void 0,
      bytes: progressBytes,
      rate: rate ? rate : void 0,
      estimated: rate && total && inRange ? (total - loaded) / rate : void 0,
      event: e
    };
    data[isDownloadStream ? "download" : "upload"] = true;
    listener(data);
  };
}
const isXHRAdapterSupported = typeof XMLHttpRequest !== "undefined";
var xhrAdapter = isXHRAdapterSupported && function(config) {
  return new Promise(function dispatchXhrRequest(resolve, reject) {
    let requestData = config.data;
    const requestHeaders = AxiosHeaders.from(config.headers).normalize();
    const responseType = config.responseType;
    let onCanceled;
    function done() {
      if (config.cancelToken) {
        config.cancelToken.unsubscribe(onCanceled);
      }
      if (config.signal) {
        config.signal.removeEventListener("abort", onCanceled);
      }
    }
    if (utils.isFormData(requestData) && platform.isStandardBrowserEnv) {
      requestHeaders.setContentType(false);
    }
    let request = new XMLHttpRequest();
    if (config.auth) {
      const username = config.auth.username || "";
      const password = config.auth.password ? unescape(encodeURIComponent(config.auth.password)) : "";
      requestHeaders.set("Authorization", "Basic " + btoa(username + ":" + password));
    }
    const fullPath = buildFullPath(config.baseURL, config.url);
    request.open(config.method.toUpperCase(), buildURL(fullPath, config.params, config.paramsSerializer), true);
    request.timeout = config.timeout;
    function onloadend() {
      if (!request) {
        return;
      }
      const responseHeaders = AxiosHeaders.from("getAllResponseHeaders" in request && request.getAllResponseHeaders());
      const responseData = !responseType || responseType === "text" || responseType === "json" ? request.responseText : request.response;
      const response = {
        data: responseData,
        status: request.status,
        statusText: request.statusText,
        headers: responseHeaders,
        config,
        request
      };
      settle(function _resolve(value) {
        resolve(value);
        done();
      }, function _reject(err) {
        reject(err);
        done();
      }, response);
      request = null;
    }
    if ("onloadend" in request) {
      request.onloadend = onloadend;
    } else {
      request.onreadystatechange = function handleLoad() {
        if (!request || request.readyState !== 4) {
          return;
        }
        if (request.status === 0 && !(request.responseURL && request.responseURL.indexOf("file:") === 0)) {
          return;
        }
        setTimeout(onloadend);
      };
    }
    request.onabort = function handleAbort() {
      if (!request) {
        return;
      }
      reject(new AxiosError("Request aborted", AxiosError.ECONNABORTED, config, request));
      request = null;
    };
    request.onerror = function handleError() {
      reject(new AxiosError("Network Error", AxiosError.ERR_NETWORK, config, request));
      request = null;
    };
    request.ontimeout = function handleTimeout() {
      let timeoutErrorMessage = config.timeout ? "timeout of " + config.timeout + "ms exceeded" : "timeout exceeded";
      const transitional2 = config.transitional || transitionalDefaults;
      if (config.timeoutErrorMessage) {
        timeoutErrorMessage = config.timeoutErrorMessage;
      }
      reject(new AxiosError(timeoutErrorMessage, transitional2.clarifyTimeoutError ? AxiosError.ETIMEDOUT : AxiosError.ECONNABORTED, config, request));
      request = null;
    };
    if (platform.isStandardBrowserEnv) {
      const xsrfValue = (config.withCredentials || isURLSameOrigin(fullPath)) && config.xsrfCookieName && cookies.read(config.xsrfCookieName);
      if (xsrfValue) {
        requestHeaders.set(config.xsrfHeaderName, xsrfValue);
      }
    }
    requestData === void 0 && requestHeaders.setContentType(null);
    if ("setRequestHeader" in request) {
      utils.forEach(requestHeaders.toJSON(), function setRequestHeader(val, key) {
        request.setRequestHeader(key, val);
      });
    }
    if (!utils.isUndefined(config.withCredentials)) {
      request.withCredentials = !!config.withCredentials;
    }
    if (responseType && responseType !== "json") {
      request.responseType = config.responseType;
    }
    if (typeof config.onDownloadProgress === "function") {
      request.addEventListener("progress", progressEventReducer(config.onDownloadProgress, true));
    }
    if (typeof config.onUploadProgress === "function" && request.upload) {
      request.upload.addEventListener("progress", progressEventReducer(config.onUploadProgress));
    }
    if (config.cancelToken || config.signal) {
      onCanceled = (cancel) => {
        if (!request) {
          return;
        }
        reject(!cancel || cancel.type ? new CanceledError(null, config, request) : cancel);
        request.abort();
        request = null;
      };
      config.cancelToken && config.cancelToken.subscribe(onCanceled);
      if (config.signal) {
        config.signal.aborted ? onCanceled() : config.signal.addEventListener("abort", onCanceled);
      }
    }
    const protocol = parseProtocol(fullPath);
    if (protocol && platform.protocols.indexOf(protocol) === -1) {
      reject(new AxiosError("Unsupported protocol " + protocol + ":", AxiosError.ERR_BAD_REQUEST, config));
      return;
    }
    request.send(requestData || null);
  });
};
const knownAdapters = {
  http: httpAdapter,
  xhr: xhrAdapter
};
utils.forEach(knownAdapters, (fn, value) => {
  if (fn) {
    try {
      Object.defineProperty(fn, "name", {value});
    } catch (e) {
    }
    Object.defineProperty(fn, "adapterName", {value});
  }
});
var adapters = {
  getAdapter: (adapters2) => {
    adapters2 = utils.isArray(adapters2) ? adapters2 : [adapters2];
    const {length} = adapters2;
    let nameOrAdapter;
    let adapter;
    for (let i = 0; i < length; i++) {
      nameOrAdapter = adapters2[i];
      if (adapter = utils.isString(nameOrAdapter) ? knownAdapters[nameOrAdapter.toLowerCase()] : nameOrAdapter) {
        break;
      }
    }
    if (!adapter) {
      if (adapter === false) {
        throw new AxiosError(`Adapter ${nameOrAdapter} is not supported by the environment`, "ERR_NOT_SUPPORT");
      }
      throw new Error(utils.hasOwnProp(knownAdapters, nameOrAdapter) ? `Adapter '${nameOrAdapter}' is not available in the build` : `Unknown adapter '${nameOrAdapter}'`);
    }
    if (!utils.isFunction(adapter)) {
      throw new TypeError("adapter is not a function");
    }
    return adapter;
  },
  adapters: knownAdapters
};
function throwIfCancellationRequested(config) {
  if (config.cancelToken) {
    config.cancelToken.throwIfRequested();
  }
  if (config.signal && config.signal.aborted) {
    throw new CanceledError();
  }
}
function dispatchRequest(config) {
  throwIfCancellationRequested(config);
  config.headers = AxiosHeaders.from(config.headers);
  config.data = transformData.call(config, config.transformRequest);
  if (["post", "put", "patch"].indexOf(config.method) !== -1) {
    config.headers.setContentType("application/x-www-form-urlencoded", false);
  }
  const adapter = adapters.getAdapter(config.adapter || defaults.adapter);
  return adapter(config).then(function onAdapterResolution(response) {
    throwIfCancellationRequested(config);
    response.data = transformData.call(config, config.transformResponse, response);
    response.headers = AxiosHeaders.from(response.headers);
    return response;
  }, function onAdapterRejection(reason) {
    if (!isCancel(reason)) {
      throwIfCancellationRequested(config);
      if (reason && reason.response) {
        reason.response.data = transformData.call(config, config.transformResponse, reason.response);
        reason.response.headers = AxiosHeaders.from(reason.response.headers);
      }
    }
    return Promise.reject(reason);
  });
}
const headersToObject = (thing) => thing instanceof AxiosHeaders ? thing.toJSON() : thing;
function mergeConfig(config1, config2) {
  config2 = config2 || {};
  const config = {};
  function getMergedValue(target, source, caseless) {
    if (utils.isPlainObject(target) && utils.isPlainObject(source)) {
      return utils.merge.call({caseless}, target, source);
    } else if (utils.isPlainObject(source)) {
      return utils.merge({}, source);
    } else if (utils.isArray(source)) {
      return source.slice();
    }
    return source;
  }
  function mergeDeepProperties(a, b, caseless) {
    if (!utils.isUndefined(b)) {
      return getMergedValue(a, b, caseless);
    } else if (!utils.isUndefined(a)) {
      return getMergedValue(void 0, a, caseless);
    }
  }
  function valueFromConfig2(a, b) {
    if (!utils.isUndefined(b)) {
      return getMergedValue(void 0, b);
    }
  }
  function defaultToConfig2(a, b) {
    if (!utils.isUndefined(b)) {
      return getMergedValue(void 0, b);
    } else if (!utils.isUndefined(a)) {
      return getMergedValue(void 0, a);
    }
  }
  function mergeDirectKeys(a, b, prop) {
    if (prop in config2) {
      return getMergedValue(a, b);
    } else if (prop in config1) {
      return getMergedValue(void 0, a);
    }
  }
  const mergeMap = {
    url: valueFromConfig2,
    method: valueFromConfig2,
    data: valueFromConfig2,
    baseURL: defaultToConfig2,
    transformRequest: defaultToConfig2,
    transformResponse: defaultToConfig2,
    paramsSerializer: defaultToConfig2,
    timeout: defaultToConfig2,
    timeoutMessage: defaultToConfig2,
    withCredentials: defaultToConfig2,
    adapter: defaultToConfig2,
    responseType: defaultToConfig2,
    xsrfCookieName: defaultToConfig2,
    xsrfHeaderName: defaultToConfig2,
    onUploadProgress: defaultToConfig2,
    onDownloadProgress: defaultToConfig2,
    decompress: defaultToConfig2,
    maxContentLength: defaultToConfig2,
    maxBodyLength: defaultToConfig2,
    beforeRedirect: defaultToConfig2,
    transport: defaultToConfig2,
    httpAgent: defaultToConfig2,
    httpsAgent: defaultToConfig2,
    cancelToken: defaultToConfig2,
    socketPath: defaultToConfig2,
    responseEncoding: defaultToConfig2,
    validateStatus: mergeDirectKeys,
    headers: (a, b) => mergeDeepProperties(headersToObject(a), headersToObject(b), true)
  };
  utils.forEach(Object.keys(config1).concat(Object.keys(config2)), function computeConfigValue(prop) {
    const merge2 = mergeMap[prop] || mergeDeepProperties;
    const configValue = merge2(config1[prop], config2[prop], prop);
    utils.isUndefined(configValue) && merge2 !== mergeDirectKeys || (config[prop] = configValue);
  });
  return config;
}
const VERSION = "1.2.0";
const validators = {};
["object", "boolean", "number", "function", "string", "symbol"].forEach((type, i) => {
  validators[type] = function validator2(thing) {
    return typeof thing === type || "a" + (i < 1 ? "n " : " ") + type;
  };
});
const deprecatedWarnings = {};
validators.transitional = function transitional(validator2, version, message) {
  function formatMessage(opt, desc) {
    return "[Axios v" + VERSION + "] Transitional option '" + opt + "'" + desc + (message ? ". " + message : "");
  }
  return (value, opt, opts) => {
    if (validator2 === false) {
      throw new AxiosError(formatMessage(opt, " has been removed" + (version ? " in " + version : "")), AxiosError.ERR_DEPRECATED);
    }
    if (version && !deprecatedWarnings[opt]) {
      deprecatedWarnings[opt] = true;
      console.warn(formatMessage(opt, " has been deprecated since v" + version + " and will be removed in the near future"));
    }
    return validator2 ? validator2(value, opt, opts) : true;
  };
};
function assertOptions(options, schema, allowUnknown) {
  if (typeof options !== "object") {
    throw new AxiosError("options must be an object", AxiosError.ERR_BAD_OPTION_VALUE);
  }
  const keys = Object.keys(options);
  let i = keys.length;
  while (i-- > 0) {
    const opt = keys[i];
    const validator2 = schema[opt];
    if (validator2) {
      const value = options[opt];
      const result = value === void 0 || validator2(value, opt, options);
      if (result !== true) {
        throw new AxiosError("option " + opt + " must be " + result, AxiosError.ERR_BAD_OPTION_VALUE);
      }
      continue;
    }
    if (allowUnknown !== true) {
      throw new AxiosError("Unknown option " + opt, AxiosError.ERR_BAD_OPTION);
    }
  }
}
var validator = {
  assertOptions,
  validators
};
const validators$1 = validator.validators;
class Axios {
  constructor(instanceConfig) {
    this.defaults = instanceConfig;
    this.interceptors = {
      request: new InterceptorManager(),
      response: new InterceptorManager()
    };
  }
  request(configOrUrl, config) {
    if (typeof configOrUrl === "string") {
      config = config || {};
      config.url = configOrUrl;
    } else {
      config = configOrUrl || {};
    }
    config = mergeConfig(this.defaults, config);
    const {transitional: transitional2, paramsSerializer, headers} = config;
    if (transitional2 !== void 0) {
      validator.assertOptions(transitional2, {
        silentJSONParsing: validators$1.transitional(validators$1.boolean),
        forcedJSONParsing: validators$1.transitional(validators$1.boolean),
        clarifyTimeoutError: validators$1.transitional(validators$1.boolean)
      }, false);
    }
    if (paramsSerializer !== void 0) {
      validator.assertOptions(paramsSerializer, {
        encode: validators$1.function,
        serialize: validators$1.function
      }, true);
    }
    config.method = (config.method || this.defaults.method || "get").toLowerCase();
    let contextHeaders;
    contextHeaders = headers && utils.merge(headers.common, headers[config.method]);
    contextHeaders && utils.forEach(["delete", "get", "head", "post", "put", "patch", "common"], (method) => {
      delete headers[method];
    });
    config.headers = AxiosHeaders.concat(contextHeaders, headers);
    const requestInterceptorChain = [];
    let synchronousRequestInterceptors = true;
    this.interceptors.request.forEach(function unshiftRequestInterceptors(interceptor) {
      if (typeof interceptor.runWhen === "function" && interceptor.runWhen(config) === false) {
        return;
      }
      synchronousRequestInterceptors = synchronousRequestInterceptors && interceptor.synchronous;
      requestInterceptorChain.unshift(interceptor.fulfilled, interceptor.rejected);
    });
    const responseInterceptorChain = [];
    this.interceptors.response.forEach(function pushResponseInterceptors(interceptor) {
      responseInterceptorChain.push(interceptor.fulfilled, interceptor.rejected);
    });
    let promise;
    let i = 0;
    let len;
    if (!synchronousRequestInterceptors) {
      const chain = [dispatchRequest.bind(this), void 0];
      chain.unshift.apply(chain, requestInterceptorChain);
      chain.push.apply(chain, responseInterceptorChain);
      len = chain.length;
      promise = Promise.resolve(config);
      while (i < len) {
        promise = promise.then(chain[i++], chain[i++]);
      }
      return promise;
    }
    len = requestInterceptorChain.length;
    let newConfig = config;
    i = 0;
    while (i < len) {
      const onFulfilled = requestInterceptorChain[i++];
      const onRejected = requestInterceptorChain[i++];
      try {
        newConfig = onFulfilled(newConfig);
      } catch (error) {
        onRejected.call(this, error);
        break;
      }
    }
    try {
      promise = dispatchRequest.call(this, newConfig);
    } catch (error) {
      return Promise.reject(error);
    }
    i = 0;
    len = responseInterceptorChain.length;
    while (i < len) {
      promise = promise.then(responseInterceptorChain[i++], responseInterceptorChain[i++]);
    }
    return promise;
  }
  getUri(config) {
    config = mergeConfig(this.defaults, config);
    const fullPath = buildFullPath(config.baseURL, config.url);
    return buildURL(fullPath, config.params, config.paramsSerializer);
  }
}
utils.forEach(["delete", "get", "head", "options"], function forEachMethodNoData2(method) {
  Axios.prototype[method] = function(url, config) {
    return this.request(mergeConfig(config || {}, {
      method,
      url,
      data: (config || {}).data
    }));
  };
});
utils.forEach(["post", "put", "patch"], function forEachMethodWithData2(method) {
  function generateHTTPMethod(isForm) {
    return function httpMethod(url, data, config) {
      return this.request(mergeConfig(config || {}, {
        method,
        headers: isForm ? {
          "Content-Type": "multipart/form-data"
        } : {},
        url,
        data
      }));
    };
  }
  Axios.prototype[method] = generateHTTPMethod();
  Axios.prototype[method + "Form"] = generateHTTPMethod(true);
});
class CancelToken {
  constructor(executor) {
    if (typeof executor !== "function") {
      throw new TypeError("executor must be a function.");
    }
    let resolvePromise;
    this.promise = new Promise(function promiseExecutor(resolve) {
      resolvePromise = resolve;
    });
    const token = this;
    this.promise.then((cancel) => {
      if (!token._listeners)
        return;
      let i = token._listeners.length;
      while (i-- > 0) {
        token._listeners[i](cancel);
      }
      token._listeners = null;
    });
    this.promise.then = (onfulfilled) => {
      let _resolve;
      const promise = new Promise((resolve) => {
        token.subscribe(resolve);
        _resolve = resolve;
      }).then(onfulfilled);
      promise.cancel = function reject() {
        token.unsubscribe(_resolve);
      };
      return promise;
    };
    executor(function cancel(message, config, request) {
      if (token.reason) {
        return;
      }
      token.reason = new CanceledError(message, config, request);
      resolvePromise(token.reason);
    });
  }
  throwIfRequested() {
    if (this.reason) {
      throw this.reason;
    }
  }
  subscribe(listener) {
    if (this.reason) {
      listener(this.reason);
      return;
    }
    if (this._listeners) {
      this._listeners.push(listener);
    } else {
      this._listeners = [listener];
    }
  }
  unsubscribe(listener) {
    if (!this._listeners) {
      return;
    }
    const index = this._listeners.indexOf(listener);
    if (index !== -1) {
      this._listeners.splice(index, 1);
    }
  }
  static source() {
    let cancel;
    const token = new CancelToken(function executor(c) {
      cancel = c;
    });
    return {
      token,
      cancel
    };
  }
}
function spread(callback) {
  return function wrap(arr) {
    return callback.apply(null, arr);
  };
}
function isAxiosError(payload) {
  return utils.isObject(payload) && payload.isAxiosError === true;
}
function createInstance(defaultConfig) {
  const context = new Axios(defaultConfig);
  const instance = bind(Axios.prototype.request, context);
  utils.extend(instance, Axios.prototype, context, {allOwnKeys: true});
  utils.extend(instance, context, null, {allOwnKeys: true});
  instance.create = function create(instanceConfig) {
    return createInstance(mergeConfig(defaultConfig, instanceConfig));
  };
  return instance;
}
const axios = createInstance(defaults);
axios.Axios = Axios;
axios.CanceledError = CanceledError;
axios.CancelToken = CancelToken;
axios.isCancel = isCancel;
axios.VERSION = VERSION;
axios.toFormData = toFormData;
axios.AxiosError = AxiosError;
axios.Cancel = axios.CanceledError;
axios.all = function all(promises) {
  return Promise.all(promises);
};
axios.spread = spread;
axios.isAxiosError = isAxiosError;
axios.AxiosHeaders = AxiosHeaders;
axios.formToJSON = (thing) => formDataToJSON(utils.isHTMLForm(thing) ? new FormData(thing) : thing);
axios.default = axios;

/* generated by Svelte v3.59.1 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[17] = list[i].label;
	child_ctx[18] = list[i].type;
	child_ctx[19] = list[i].placeholder;
	child_ctx[20] = list[i].required;
	child_ctx[23] = i;
	const constants_0 = `${/*label*/ child_ctx[17]}-${/*i*/ child_ctx[23]}`;
	child_ctx[21] = constants_0;
	return child_ctx;
}

function get_each_context_1$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[24] = list[i].icon;
	child_ctx[17] = list[i].label;
	return child_ctx;
}

// (169:8) {#each list_items as { icon, label }}
function create_each_block_1$1(ctx) {
	let li;
	let span0;
	let icon;
	let t0;
	let span1;
	let t1_value = /*label*/ ctx[17] + "";
	let t1;
	let t2;
	let current;
	icon = new Component$1({ props: { icon: /*icon*/ ctx[24] } });

	return {
		c() {
			li = element("li");
			span0 = element("span");
			create_component(icon.$$.fragment);
			t0 = space();
			span1 = element("span");
			t1 = text(t1_value);
			t2 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			span0 = claim_element(li_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			claim_component(icon.$$.fragment, span0_nodes);
			span0_nodes.forEach(detach);
			t0 = claim_space(li_nodes);
			span1 = claim_element(li_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t1 = claim_text(span1_nodes, t1_value);
			span1_nodes.forEach(detach);
			t2 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "icon svelte-cowe8h");
			attr(span1, "class", "label");
			attr(li, "class", "svelte-cowe8h");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, span0);
			mount_component(icon, span0, null);
			append_hydration(li, t0);
			append_hydration(li, span1);
			append_hydration(span1, t1);
			append_hydration(li, t2);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*list_items*/ 4) icon_changes.icon = /*icon*/ ctx[24];
			icon.$set(icon_changes);
			if ((!current || dirty & /*list_items*/ 4) && t1_value !== (t1_value = /*label*/ ctx[17] + "")) set_data(t1, t1_value);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(icon);
		}
	};
}

// (240:22) 
function create_if_block_7(ctx) {
	let div;
	let html_tag;
	let raw_value = /*form*/ ctx[3].submission_error + "";
	let t0;
	let button;
	let icon;
	let t1;
	let span;
	let t2;
	let current;
	let mounted;
	let dispose;
	icon = new Component$1({ props: { icon: "mdi:arrow-left-thin" } });

	return {
		c() {
			div = element("div");
			html_tag = new HtmlTagHydration(false);
			t0 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t1 = space();
			span = element("span");
			t2 = text("Try again");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			html_tag = claim_html_tag(div_nodes, false);
			t0 = claim_space(div_nodes);
			button = claim_element(div_nodes, "BUTTON", {});
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			t1 = claim_space(button_nodes);
			span = claim_element(button_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t2 = claim_text(span_nodes, "Try again");
			span_nodes.forEach(detach);
			button_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			html_tag.a = t0;
			attr(span, "class", "svelte-cowe8h");
			attr(div, "class", "section-container content svelte-cowe8h");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			html_tag.m(raw_value, div);
			append_hydration(div, t0);
			append_hydration(div, button);
			mount_component(icon, button, null);
			append_hydration(button, t1);
			append_hydration(button, span);
			append_hydration(span, t2);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[16]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if ((!current || dirty & /*form*/ 8) && raw_value !== (raw_value = /*form*/ ctx[3].submission_error + "")) html_tag.p(raw_value);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);
			destroy_component(icon);
			mounted = false;
			dispose();
		}
	};
}

// (232:26) 
function create_if_block_6(ctx) {
	let div;
	let html_tag;
	let raw_value = /*form*/ ctx[3].submission_confirmation + "";
	let t0;
	let button;
	let icon;
	let t1;
	let span;
	let t2;
	let current;
	let mounted;
	let dispose;
	icon = new Component$1({ props: { icon: "mdi:arrow-left-thin" } });

	return {
		c() {
			div = element("div");
			html_tag = new HtmlTagHydration(false);
			t0 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t1 = space();
			span = element("span");
			t2 = text("Resubmit");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			html_tag = claim_html_tag(div_nodes, false);
			t0 = claim_space(div_nodes);
			button = claim_element(div_nodes, "BUTTON", {});
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			t1 = claim_space(button_nodes);
			span = claim_element(button_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t2 = claim_text(span_nodes, "Resubmit");
			span_nodes.forEach(detach);
			button_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			html_tag.a = t0;
			attr(span, "class", "svelte-cowe8h");
			attr(div, "class", "section-container content svelte-cowe8h");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			html_tag.m(raw_value, div);
			append_hydration(div, t0);
			append_hydration(div, button);
			mount_component(icon, button, null);
			append_hydration(button, t1);
			append_hydration(button, span);
			append_hydration(span, t2);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[15]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if ((!current || dirty & /*form*/ 8) && raw_value !== (raw_value = /*form*/ ctx[3].submission_confirmation + "")) html_tag.p(raw_value);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);
			destroy_component(icon);
			mounted = false;
			dispose();
		}
	};
}

// (180:6) {#if !submitted && !error}
function create_if_block$2(ctx) {
	let form_1;
	let t0;
	let button;
	let icon;
	let t1;
	let span;
	let t2;
	let current;
	let mounted;
	let dispose;
	let each_value = /*form*/ ctx[3].fields;
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	icon = new Component$1({
			props: { icon: "carbon:send-alt-filled" }
		});

	return {
		c() {
			form_1 = element("form");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t0 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t1 = space();
			span = element("span");
			t2 = text("Submit");
			this.h();
		},
		l(nodes) {
			form_1 = claim_element(nodes, "FORM", { class: true });
			var form_1_nodes = children(form_1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(form_1_nodes);
			}

			t0 = claim_space(form_1_nodes);
			button = claim_element(form_1_nodes, "BUTTON", { type: true, class: true });
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			t1 = claim_space(button_nodes);
			span = claim_element(button_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t2 = claim_text(span_nodes, "Submit");
			span_nodes.forEach(detach);
			button_nodes.forEach(detach);
			form_1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "svelte-cowe8h");
			attr(button, "type", "submit");
			attr(button, "class", "button");
			attr(form_1, "class", "svelte-cowe8h");
		},
		m(target, anchor) {
			insert_hydration(target, form_1, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(form_1, null);
				}
			}

			append_hydration(form_1, t0);
			append_hydration(form_1, button);
			mount_component(icon, button, null);
			append_hydration(button, t1);
			append_hydration(button, span);
			append_hydration(span, t2);
			current = true;

			if (!mounted) {
				dispose = listen(form_1, "submit", prevent_default(/*submit_form*/ ctx[8]));
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*form, add_file, files*/ 152) {
				each_value = /*form*/ ctx[3].fields;
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(form_1, t0);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(form_1);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			mounted = false;
			dispose();
		}
	};
}

// (215:12) {:else}
function create_else_block$1(ctx) {
	let label;
	let span;
	let t0_value = /*label*/ ctx[17] + "";
	let t0;
	let t1;
	let t2;
	let input;
	let input_name_value;
	let input_placeholder_value;
	let if_block = /*required*/ ctx[20] && create_if_block_5();

	return {
		c() {
			label = element("label");
			span = element("span");
			t0 = text(t0_value);
			t1 = space();
			if (if_block) if_block.c();
			t2 = space();
			input = element("input");
			this.h();
		},
		l(nodes) {
			label = claim_element(nodes, "LABEL", { class: true });
			var label_nodes = children(label);
			span = claim_element(label_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, t0_value);
			t1 = claim_space(span_nodes);
			if (if_block) if_block.l(span_nodes);
			span_nodes.forEach(detach);
			t2 = claim_space(label_nodes);

			input = claim_element(label_nodes, "INPUT", {
				type: true,
				name: true,
				placeholder: true,
				class: true
			});

			label_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "svelte-cowe8h");
			attr(input, "type", "text");
			attr(input, "name", input_name_value = /*label*/ ctx[17]);
			attr(input, "placeholder", input_placeholder_value = /*placeholder*/ ctx[19]);
			attr(input, "class", "svelte-cowe8h");
			attr(label, "class", "svelte-cowe8h");
		},
		m(target, anchor) {
			insert_hydration(target, label, anchor);
			append_hydration(label, span);
			append_hydration(span, t0);
			append_hydration(span, t1);
			if (if_block) if_block.m(span, null);
			append_hydration(label, t2);
			append_hydration(label, input);
		},
		p(ctx, dirty) {
			if (dirty & /*form*/ 8 && t0_value !== (t0_value = /*label*/ ctx[17] + "")) set_data(t0, t0_value);

			if (/*required*/ ctx[20]) {
				if (if_block) ; else {
					if_block = create_if_block_5();
					if_block.c();
					if_block.m(span, null);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if (dirty & /*form*/ 8 && input_name_value !== (input_name_value = /*label*/ ctx[17])) {
				attr(input, "name", input_name_value);
			}

			if (dirty & /*form*/ 8 && input_placeholder_value !== (input_placeholder_value = /*placeholder*/ ctx[19])) {
				attr(input, "placeholder", input_placeholder_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(label);
			if (if_block) if_block.d();
		}
	};
}

// (206:42) 
function create_if_block_3$1(ctx) {
	let label;
	let span;
	let t0_value = /*label*/ ctx[17] + "";
	let t0;
	let t1;
	let t2;
	let textarea;
	let textarea_name_value;
	let textarea_placeholder_value;
	let if_block = /*required*/ ctx[20] && create_if_block_4$1();

	return {
		c() {
			label = element("label");
			span = element("span");
			t0 = text(t0_value);
			t1 = space();
			if (if_block) if_block.c();
			t2 = space();
			textarea = element("textarea");
			this.h();
		},
		l(nodes) {
			label = claim_element(nodes, "LABEL", { class: true });
			var label_nodes = children(label);
			span = claim_element(label_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, t0_value);
			t1 = claim_space(span_nodes);
			if (if_block) if_block.l(span_nodes);
			span_nodes.forEach(detach);
			t2 = claim_space(label_nodes);

			textarea = claim_element(label_nodes, "TEXTAREA", {
				name: true,
				placeholder: true,
				class: true
			});

			children(textarea).forEach(detach);
			label_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "svelte-cowe8h");
			attr(textarea, "name", textarea_name_value = /*label*/ ctx[17]);
			attr(textarea, "placeholder", textarea_placeholder_value = /*placeholder*/ ctx[19]);
			attr(textarea, "class", "svelte-cowe8h");
			attr(label, "class", "has-textarea svelte-cowe8h");
		},
		m(target, anchor) {
			insert_hydration(target, label, anchor);
			append_hydration(label, span);
			append_hydration(span, t0);
			append_hydration(span, t1);
			if (if_block) if_block.m(span, null);
			append_hydration(label, t2);
			append_hydration(label, textarea);
		},
		p(ctx, dirty) {
			if (dirty & /*form*/ 8 && t0_value !== (t0_value = /*label*/ ctx[17] + "")) set_data(t0, t0_value);

			if (/*required*/ ctx[20]) {
				if (if_block) ; else {
					if_block = create_if_block_4$1();
					if_block.c();
					if_block.m(span, null);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if (dirty & /*form*/ 8 && textarea_name_value !== (textarea_name_value = /*label*/ ctx[17])) {
				attr(textarea, "name", textarea_name_value);
			}

			if (dirty & /*form*/ 8 && textarea_placeholder_value !== (textarea_placeholder_value = /*placeholder*/ ctx[19])) {
				attr(textarea, "placeholder", textarea_placeholder_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(label);
			if (if_block) if_block.d();
		}
	};
}

// (184:12) {#if type === "file"}
function create_if_block_1$2(ctx) {
	let label;
	let span0;
	let t0_value = /*label*/ ctx[17] + "";
	let t0;
	let t1;
	let t2;
	let div;
	let span1;
	let t3_value = (/*files*/ ctx[4][/*id*/ ctx[21]] || "Choose file") + "";
	let t3;
	let t4;
	let span2;
	let t5;
	let icon;
	let t6;
	let input;
	let input_name_value;
	let current;
	let mounted;
	let dispose;
	let if_block = /*required*/ ctx[20] && create_if_block_2$1();
	icon = new Component$1({ props: { icon: "ep:upload-filled" } });

	function change_handler(...args) {
		return /*change_handler*/ ctx[14](/*id*/ ctx[21], ...args);
	}

	return {
		c() {
			label = element("label");
			span0 = element("span");
			t0 = text(t0_value);
			t1 = space();
			if (if_block) if_block.c();
			t2 = space();
			div = element("div");
			span1 = element("span");
			t3 = text(t3_value);
			t4 = space();
			span2 = element("span");
			t5 = text("Choose\n                    ");
			create_component(icon.$$.fragment);
			t6 = space();
			input = element("input");
			this.h();
		},
		l(nodes) {
			label = claim_element(nodes, "LABEL", { class: true });
			var label_nodes = children(label);
			span0 = claim_element(label_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t0 = claim_text(span0_nodes, t0_value);
			t1 = claim_space(span0_nodes);
			if (if_block) if_block.l(span0_nodes);
			span0_nodes.forEach(detach);
			t2 = claim_space(label_nodes);
			div = claim_element(label_nodes, "DIV", { class: true });
			var div_nodes = children(div);
			span1 = claim_element(div_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t3 = claim_text(span1_nodes, t3_value);
			span1_nodes.forEach(detach);
			t4 = claim_space(div_nodes);
			span2 = claim_element(div_nodes, "SPAN", { class: true });
			var span2_nodes = children(span2);
			t5 = claim_text(span2_nodes, "Choose\n                    ");
			claim_component(icon.$$.fragment, span2_nodes);
			span2_nodes.forEach(detach);
			div_nodes.forEach(detach);
			t6 = claim_space(label_nodes);
			input = claim_element(label_nodes, "INPUT", { name: true, type: true, class: true });
			label_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "svelte-cowe8h");
			attr(span1, "class", "button-left svelte-cowe8h");
			attr(span2, "class", "button-right svelte-cowe8h");
			attr(div, "class", "field-item svelte-cowe8h");
			attr(input, "name", input_name_value = /*label*/ ctx[17]);
			attr(input, "type", "file");
			attr(input, "class", "svelte-cowe8h");
			attr(label, "class", "file svelte-cowe8h");
		},
		m(target, anchor) {
			insert_hydration(target, label, anchor);
			append_hydration(label, span0);
			append_hydration(span0, t0);
			append_hydration(span0, t1);
			if (if_block) if_block.m(span0, null);
			append_hydration(label, t2);
			append_hydration(label, div);
			append_hydration(div, span1);
			append_hydration(span1, t3);
			append_hydration(div, t4);
			append_hydration(div, span2);
			append_hydration(span2, t5);
			mount_component(icon, span2, null);
			append_hydration(label, t6);
			append_hydration(label, input);
			current = true;

			if (!mounted) {
				dispose = listen(input, "change", change_handler);
				mounted = true;
			}
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;
			if ((!current || dirty & /*form*/ 8) && t0_value !== (t0_value = /*label*/ ctx[17] + "")) set_data(t0, t0_value);

			if (/*required*/ ctx[20]) {
				if (if_block) ; else {
					if_block = create_if_block_2$1();
					if_block.c();
					if_block.m(span0, null);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if ((!current || dirty & /*files, form*/ 24) && t3_value !== (t3_value = (/*files*/ ctx[4][/*id*/ ctx[21]] || "Choose file") + "")) set_data(t3, t3_value);

			if (!current || dirty & /*form*/ 8 && input_name_value !== (input_name_value = /*label*/ ctx[17])) {
				attr(input, "name", input_name_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(label);
			if (if_block) if_block.d();
			destroy_component(icon);
			mounted = false;
			dispose();
		}
	};
}

// (219:18) {#if required}
function create_if_block_5(ctx) {
	let span;
	let t;

	return {
		c() {
			span = element("span");
			t = text("*");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t = claim_text(span_nodes, "*");
			span_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "required svelte-cowe8h");
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
			append_hydration(span, t);
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (210:18) {#if required}
function create_if_block_4$1(ctx) {
	let span;
	let t;

	return {
		c() {
			span = element("span");
			t = text("*");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t = claim_text(span_nodes, "*");
			span_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "required svelte-cowe8h");
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
			append_hydration(span, t);
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (188:18) {#if required}
function create_if_block_2$1(ctx) {
	let span;
	let t;

	return {
		c() {
			span = element("span");
			t = text("*");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t = claim_text(span_nodes, "*");
			span_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "required svelte-cowe8h");
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
			append_hydration(span, t);
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (182:10) {#each form.fields as { label, type, placeholder, required }
function create_each_block$1(ctx) {
	let current_block_type_index;
	let if_block;
	let if_block_anchor;
	let current;
	const if_block_creators = [create_if_block_1$2, create_if_block_3$1, create_else_block$1];
	const if_blocks = [];

	function select_block_type_1(ctx, dirty) {
		if (/*type*/ ctx[18] === "file") return 0;
		if (/*type*/ ctx[18] === "textarea") return 1;
		return 2;
	}

	current_block_type_index = select_block_type_1(ctx);
	if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_blocks[current_block_type_index].m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
			current = true;
		},
		p(ctx, dirty) {
			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type_1(ctx);

			if (current_block_type_index === previous_block_index) {
				if_blocks[current_block_type_index].p(ctx, dirty);
			} else {
				group_outros();

				transition_out(if_blocks[previous_block_index], 1, 1, () => {
					if_blocks[previous_block_index] = null;
				});

				check_outros();
				if_block = if_blocks[current_block_type_index];

				if (!if_block) {
					if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
					if_block.c();
				} else {
					if_block.p(ctx, dirty);
				}

				transition_in(if_block, 1);
				if_block.m(if_block_anchor.parentNode, if_block_anchor);
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if_blocks[current_block_type_index].d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function create_fragment$3(ctx) {
	let div3;
	let section;
	let div2;
	let div0;
	let h2;
	let t0;
	let t1;
	let h3;
	let t2;
	let t3;
	let ul;
	let t4;
	let div1;
	let current_block_type_index;
	let if_block;
	let current;
	let each_value_1 = /*list_items*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1$1(get_each_context_1$1(ctx, each_value_1, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	const if_block_creators = [create_if_block$2, create_if_block_6, create_if_block_7];
	const if_blocks = [];

	function select_block_type(ctx, dirty) {
		if (!/*submitted*/ ctx[5] && !/*error*/ ctx[6]) return 0;
		if (/*submitted*/ ctx[5]) return 1;
		if (/*error*/ ctx[6]) return 2;
		return -1;
	}

	if (~(current_block_type_index = select_block_type(ctx))) {
		if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
	}

	return {
		c() {
			div3 = element("div");
			section = element("section");
			div2 = element("div");
			div0 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			h3 = element("h3");
			t2 = text(/*subheading*/ ctx[1]);
			t3 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t4 = space();
			div1 = element("div");
			if (if_block) if_block.c();
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			section = claim_element(div3_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div2 = claim_element(section_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			h3 = claim_element(div0_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t2 = claim_text(h3_nodes, /*subheading*/ ctx[1]);
			h3_nodes.forEach(detach);
			t3 = claim_space(div0_nodes);
			ul = claim_element(div0_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t4 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			if (if_block) if_block.l(div1_nodes);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading");
			attr(h3, "class", "subheading svelte-cowe8h");
			attr(ul, "class", "svelte-cowe8h");
			attr(div0, "class", "main svelte-cowe8h");
			attr(div1, "class", "card svelte-cowe8h");
			attr(div2, "class", "section-container svelte-cowe8h");
			attr(section, "class", "svelte-cowe8h");
			attr(div3, "class", "section");
			attr(div3, "id", "section-f91dbadd");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, section);
			append_hydration(section, div2);
			append_hydration(div2, div0);
			append_hydration(div0, h2);
			append_hydration(h2, t0);
			append_hydration(div0, t1);
			append_hydration(div0, h3);
			append_hydration(h3, t2);
			append_hydration(div0, t3);
			append_hydration(div0, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			append_hydration(div2, t4);
			append_hydration(div2, div1);

			if (~current_block_type_index) {
				if_blocks[current_block_type_index].m(div1, null);
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (!current || dirty & /*subheading*/ 2) set_data(t2, /*subheading*/ ctx[1]);

			if (dirty & /*list_items*/ 4) {
				each_value_1 = /*list_items*/ ctx[2];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block_1$1(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value_1.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}

			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type(ctx);

			if (current_block_type_index === previous_block_index) {
				if (~current_block_type_index) {
					if_blocks[current_block_type_index].p(ctx, dirty);
				}
			} else {
				if (if_block) {
					group_outros();

					transition_out(if_blocks[previous_block_index], 1, 1, () => {
						if_blocks[previous_block_index] = null;
					});

					check_outros();
				}

				if (~current_block_type_index) {
					if_block = if_blocks[current_block_type_index];

					if (!if_block) {
						if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
						if_block.c();
					} else {
						if_block.p(ctx, dirty);
					}

					transition_in(if_block, 1);
					if_block.m(div1, null);
				} else {
					if_block = null;
				}
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value_1.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			transition_in(if_block);
			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);
			destroy_each(each_blocks, detaching);

			if (~current_block_type_index) {
				if_blocks[current_block_type_index].d();
			}
		}
	};
}

function get_form_data(form) {
	const form_data = new FormData(form);
	var object = {};

	form_data.forEach((value, key) => {
		object[key] = value;
	});

	return object;
}

function instance$3($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { primary_cta } = $$props;
	let { footer_links } = $$props;
	let { company_description } = $$props;
	let { heading } = $$props;
	let { subheading } = $$props;
	let { list_items } = $$props;
	let { form } = $$props;

	// Store file names to display them in the file field
	const files = {};

	function add_file({ id, e }) {
		const file_name = e.target.value.split("\\").pop();
		$$invalidate(4, files[id] = file_name, files);
	}

	let submitted = false;
	let error = false;

	async function submit_form(e) {
		const form_data = get_form_data(e.target);
		const { data } = await axios.post(form_endpoint, form_data).catch(e => ({ data: null }));

		if (data) {
			$$invalidate(5, submitted = true);
		} else {
			$$invalidate(6, error = true);
		}
	}

	const change_handler = (id, e) => add_file({ id, e });
	const click_handler = () => $$invalidate(5, submitted = false);
	const click_handler_1 = () => $$invalidate(6, error = false);

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(9, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(10, site_nav = $$props.site_nav);
		if ('primary_cta' in $$props) $$invalidate(11, primary_cta = $$props.primary_cta);
		if ('footer_links' in $$props) $$invalidate(12, footer_links = $$props.footer_links);
		if ('company_description' in $$props) $$invalidate(13, company_description = $$props.company_description);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(1, subheading = $$props.subheading);
		if ('list_items' in $$props) $$invalidate(2, list_items = $$props.list_items);
		if ('form' in $$props) $$invalidate(3, form = $$props.form);
	};

	return [
		heading,
		subheading,
		list_items,
		form,
		files,
		submitted,
		error,
		add_file,
		submit_form,
		logo,
		site_nav,
		primary_cta,
		footer_links,
		company_description,
		change_handler,
		click_handler,
		click_handler_1
	];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			logo: 9,
			site_nav: 10,
			primary_cta: 11,
			footer_links: 12,
			company_description: 13,
			heading: 0,
			subheading: 1,
			list_items: 2,
			form: 3
		});
	}
}

/* generated by Svelte v3.59.1 */

function get_each_context$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[5] = list[i].label;
	child_ctx[6] = list[i].link_list;
	return child_ctx;
}

function get_each_context_1$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].link;
	return child_ctx;
}

// (100:31) 
function create_if_block_1$3(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (98:6) {#if logo.title}
function create_if_block$3(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (111:10) {#each link_list as { link }}
function create_each_block_1$2(ctx) {
	let a;
	let t_value = /*link*/ ctx[9].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-gkcc88");
			attr(a, "href", a_href_value = /*link*/ ctx[9].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*footer_links*/ 2 && t_value !== (t_value = /*link*/ ctx[9].label + "")) set_data(t, t_value);

			if (dirty & /*footer_links*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[9].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (107:4) {#each footer_links as { label, link_list }}
function create_each_block$2(ctx) {
	let div;
	let h4;
	let t0_value = /*label*/ ctx[5] + "";
	let t0;
	let t1;
	let nav;
	let t2;
	let each_value_1 = /*link_list*/ ctx[6];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1$2(get_each_context_1$2(ctx, each_value_1, i));
	}

	return {
		c() {
			div = element("div");
			h4 = element("h4");
			t0 = text(t0_value);
			t1 = space();
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t2 = space();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			h4 = claim_element(div_nodes, "H4", { class: true });
			var h4_nodes = children(h4);
			t0 = claim_text(h4_nodes, t0_value);
			h4_nodes.forEach(detach);
			t1 = claim_space(div_nodes);
			nav = claim_element(div_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			nav_nodes.forEach(detach);
			t2 = claim_space(div_nodes);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h4, "class", "label svelte-gkcc88");
			attr(nav, "class", "svelte-gkcc88");
			attr(div, "class", "item svelte-gkcc88");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, h4);
			append_hydration(h4, t0);
			append_hydration(div, t1);
			append_hydration(div, nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(div, t2);
		},
		p(ctx, dirty) {
			if (dirty & /*footer_links*/ 2 && t0_value !== (t0_value = /*label*/ ctx[5] + "")) set_data(t0, t0_value);

			if (dirty & /*footer_links*/ 2) {
				each_value_1 = /*link_list*/ ctx[6];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$2(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1$2(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}
		},
		d(detaching) {
			if (detaching) detach(div);
			destroy_each(each_blocks, detaching);
		}
	};
}

function create_fragment$4(ctx) {
	let div4;
	let footer;
	let div1;
	let a0;
	let t0;
	let div0;
	let raw_value = /*company_description*/ ctx[2].html + "";
	let t1;
	let div2;
	let t2;
	let div3;
	let span;
	let a1;
	let t3;
	let t4;

	function select_block_type(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block$3;
		if (/*logo*/ ctx[0].image.url) return create_if_block_1$3;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type && current_block_type(ctx);
	let each_value = /*footer_links*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$2(get_each_context$2(ctx, each_value, i));
	}

	return {
		c() {
			div4 = element("div");
			footer = element("footer");
			div1 = element("div");
			a0 = element("a");
			if (if_block) if_block.c();
			t0 = space();
			div0 = element("div");
			t1 = space();
			div2 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t2 = space();
			div3 = element("div");
			span = element("span");
			a1 = element("a");
			t3 = text("Primo");
			t4 = text(" Powered");
			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			footer = claim_element(div4_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			div1 = claim_element(footer_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a0 = claim_element(div1_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			if (if_block) if_block.l(a0_nodes);
			a0_nodes.forEach(detach);
			t0 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t1 = claim_space(footer_nodes);
			div2 = claim_element(footer_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div2_nodes);
			}

			div2_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			t2 = claim_space(div4_nodes);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			span = claim_element(div3_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			a1 = claim_element(span_nodes, "A", { href: true, class: true });
			var a1_nodes = children(a1);
			t3 = claim_text(a1_nodes, "Primo");
			a1_nodes.forEach(detach);
			t4 = claim_text(span_nodes, " Powered");
			span_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "href", "/");
			attr(a0, "class", "logo");
			attr(div0, "class", "company-description svelte-gkcc88");
			attr(div1, "class", "main svelte-gkcc88");
			attr(div2, "class", "links svelte-gkcc88");
			attr(footer, "class", "section-container svelte-gkcc88");
			attr(a1, "href", "https://primo.so");
			attr(a1, "class", "svelte-gkcc88");
			attr(span, "class", "primo svelte-gkcc88");
			attr(div3, "class", "subfooter svelte-gkcc88");
			attr(div4, "class", "section");
			attr(div4, "id", "section-1cb3a088");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, footer);
			append_hydration(footer, div1);
			append_hydration(div1, a0);
			if (if_block) if_block.m(a0, null);
			append_hydration(div1, t0);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
			append_hydration(footer, t1);
			append_hydration(footer, div2);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div2, null);
				}
			}

			append_hydration(div4, t2);
			append_hydration(div4, div3);
			append_hydration(div3, span);
			append_hydration(span, a1);
			append_hydration(a1, t3);
			append_hydration(span, t4);
		},
		p(ctx, [dirty]) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if (if_block) if_block.d(1);
				if_block = current_block_type && current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(a0, null);
				}
			}

			if (dirty & /*company_description*/ 4 && raw_value !== (raw_value = /*company_description*/ ctx[2].html + "")) div0.innerHTML = raw_value;
			if (dirty & /*footer_links*/ 2) {
				each_value = /*footer_links*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$2(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$2(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div2, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div4);

			if (if_block) {
				if_block.d();
			}

			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { primary_cta } = $$props;
	let { footer_links } = $$props;
	let { company_description } = $$props;

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(3, site_nav = $$props.site_nav);
		if ('primary_cta' in $$props) $$invalidate(4, primary_cta = $$props.primary_cta);
		if ('footer_links' in $$props) $$invalidate(1, footer_links = $$props.footer_links);
		if ('company_description' in $$props) $$invalidate(2, company_description = $$props.company_description);
	};

	return [logo, footer_links, company_description, site_nav, primary_cta];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			logo: 0,
			site_nav: 3,
			primary_cta: 4,
			footer_links: 1,
			company_description: 2
		});
	}
}

/* generated by Svelte v3.59.1 */

function instance$5($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { primary_cta } = $$props;
	let { footer_links } = $$props;
	let { company_description } = $$props;

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
		if ('primary_cta' in $$props) $$invalidate(2, primary_cta = $$props.primary_cta);
		if ('footer_links' in $$props) $$invalidate(3, footer_links = $$props.footer_links);
		if ('company_description' in $$props) $$invalidate(4, company_description = $$props.company_description);
	};

	return [logo, site_nav, primary_cta, footer_links, company_description];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, null, safe_not_equal, {
			logo: 0,
			site_nav: 1,
			primary_cta: 2,
			footer_links: 3,
			company_description: 4
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$5(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let current;

	component_0 = new Component({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"url": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"size": null
					}
				},
				site_nav: [
					{ "link": { "url": "/", "label": "Home" } },
					{ "link": { "url": "/", "label": "About" } },
					{
						"link": { "url": "/services", "label": "Services" }
					}
				],
				primary_cta: { "url": "/", "label": "Free Consultation" },
				footer_links: [
					{
						"label": "Company",
						"link_list": [
							{
								"link": { "url": "/", "label": "Global location" }
							},
							{
								"link": { "url": "/", "label": "Missions" }
							},
							{
								"link": { "url": "/", "label": "Careers" }
							},
							{
								"link": { "url": "/", "label": "Investors" }
							},
							{
								"link": { "url": "/", "label": "News rooms" }
							}
						]
					},
					{
						"label": "Impact",
						"link_list": [
							{
								"link": { "url": "/", "label": "Creator awards" }
							},
							{
								"link": { "url": "/", "label": "Creative ideas" }
							},
							{
								"link": {
									"url": "/",
									"label": "Refuge initiatives"
								}
							},
							{
								"link": { "url": "/", "label": "Residents" }
							}
						]
					},
					{
						"label": "Partnership",
						"link_list": [
							{
								"link": { "url": "/", "label": "Brokers" }
							},
							{
								"link": { "url": "/", "label": "Impact coffee" }
							},
							{
								"link": { "url": "/", "label": "Table talk" }
							},
							{
								"link": { "url": "/", "label": "Push door" }
							}
						]
					}
				],
				company_description: "<p>Lorem ipsum dolor sit amet, consectetur adipiscing elit. In blandit tincidunt id turpis est platea sed.</p>"
			}
		});

	component_1 = new Component$2({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"url": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"size": null
					}
				},
				site_nav: [
					{
						"link": { "url": "/about", "label": "About" }
					},
					{
						"link": {
							"url": "/consultation",
							"label": "Consultation"
						}
					},
					{
						"link": { "url": "/services", "label": "Services" }
					}
				],
				primary_cta: {
					"url": "/consultation",
					"label": "Sign up"
				},
				footer_links: [
					{
						"label": "Company",
						"link_list": [
							{
								"link": { "url": "/", "label": "Global location" }
							},
							{
								"link": { "url": "/", "label": "Missions" }
							},
							{
								"link": { "url": "/", "label": "Careers" }
							},
							{
								"link": { "url": "/", "label": "Investors" }
							},
							{
								"link": { "url": "/", "label": "News rooms" }
							}
						]
					},
					{
						"label": "Impact",
						"link_list": [
							{
								"link": { "url": "/", "label": "Creator awards" }
							},
							{
								"link": { "url": "/", "label": "Creative ideas" }
							},
							{
								"link": {
									"url": "/",
									"label": "Refuge initiatives"
								}
							},
							{
								"link": { "url": "/", "label": "Residents" }
							}
						]
					},
					{
						"label": "Partnership",
						"link_list": [
							{
								"link": { "url": "/", "label": "Brokers" }
							},
							{
								"link": { "url": "/", "label": "Impact coffee" }
							},
							{
								"link": { "url": "/", "label": "Table talk" }
							},
							{
								"link": { "url": "/", "label": "Push door" }
							}
						]
					}
				],
				company_description: "<p>Lorem ipsum dolor sit amet, consectetur adipiscing elit. In blandit tincidunt id turpis est platea sed.</p>"
			}
		});

	component_2 = new Component$3({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"url": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"size": null
					}
				},
				site_nav: [
					{ "link": { "url": "/", "label": "Home" } },
					{ "link": { "url": "/", "label": "About" } },
					{
						"link": { "url": "/services", "label": "Services" }
					}
				],
				primary_cta: { "url": "/", "label": "Free Consultation" },
				footer_links: [
					{
						"label": "Company",
						"link_list": [
							{
								"link": { "url": "/", "label": "Global location" }
							},
							{
								"link": { "url": "/", "label": "Missions" }
							},
							{
								"link": { "url": "/", "label": "Careers" }
							},
							{
								"link": { "url": "/", "label": "Investors" }
							},
							{
								"link": { "url": "/", "label": "News rooms" }
							}
						]
					},
					{
						"label": "Impact",
						"link_list": [
							{
								"link": { "url": "/", "label": "Creator awards" }
							},
							{
								"link": { "url": "/", "label": "Creative ideas" }
							},
							{
								"link": {
									"url": "/",
									"label": "Refuge initiatives"
								}
							},
							{
								"link": { "url": "/", "label": "Residents" }
							}
						]
					},
					{
						"label": "Partnership",
						"link_list": [
							{
								"link": { "url": "/", "label": "Brokers" }
							},
							{
								"link": { "url": "/", "label": "Impact coffee" }
							},
							{
								"link": { "url": "/", "label": "Table talk" }
							},
							{
								"link": { "url": "/", "label": "Push door" }
							}
						]
					}
				],
				company_description: "<p>Lorem ipsum dolor sit amet, consectetur adipiscing elit. In blandit tincidunt id turpis est platea sed.</p>",
				heading: "Get free personal consultation today.",
				subheading: "Lorem ipsum dolor sit amet, consectetur adipiscing elit. Faucibus sed sit ultrices et sed metus sollicitudin.",
				list_items: [
					{
						"icon": "material-symbols:check-circle-rounded",
						"label": "Financial assesment report"
					},
					{
						"icon": "material-symbols:check-circle-rounded",
						"label": "Income tax planning consulting"
					},
					{
						"icon": "material-symbols:check-circle-rounded",
						"label": "Payroll and sales taxes"
					}
				],
				form: {
					"fields": [
						{
							"type": "text",
							"label": "Name",
							"required": "Ipsum magna occaecat",
							"placeholder": "Esse exercitation in"
						},
						{
							"type": "email",
							"label": "Email",
							"required": true,
							"placeholder": "johndoe@email.com"
						},
						{
							"type": "text",
							"label": "Subject",
							"required": "",
							"placeholder": "Financial and report"
						},
						{
							"type": "textarea",
							"label": "Details",
							"required": true,
							"placeholder": ""
						}
					],
					"submission_error": "<p>Something happened, your message wasn't sent.</p>",
					"submission_confirmation": "<p>Thanks for submitting that!</p>"
				}
			}
		});

	component_3 = new Component$4({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"url": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"size": null
					},
					"title": ""
				},
				site_nav: [
					{ "link": { "url": "/", "label": "Home" } },
					{ "link": { "url": "/", "label": "About" } },
					{
						"link": { "url": "/services", "label": "Services" }
					}
				],
				primary_cta: { "url": "/", "label": "Free Consultation" },
				footer_links: [
					{
						"label": "Company",
						"link_list": [
							{
								"link": { "url": "/", "label": "Our values" }
							}
						]
					},
					{
						"label": "About",
						"link_list": [
							{
								"link": { "url": "/", "label": "Learn more" }
							},
							{
								"link": { "url": "/", "label": "Our team" }
							}
						]
					},
					{
						"label": "Legal",
						"link_list": [
							{ "link": { "url": "/", "label": "ut" } },
							{
								"link": { "url": "/", "label": "adipisicing" }
							}
						]
					}
				],
				company_description: {
					"html": "<p>Trusted financial services provider offering expert guidance, customized solutions, and peace of mind for all your financial needs.</p>",
					"markdown": "Trusted financial services provider offering expert guidance, customized solutions, and peace of mind for all your financial needs.\n\n"
				}
			}
		});

	component_4 = new Component$5({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"url": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"size": null
					}
				},
				site_nav: [
					{ "link": { "url": "/", "label": "Home" } },
					{ "link": { "url": "/", "label": "About" } },
					{
						"link": { "url": "/services", "label": "Services" }
					}
				],
				primary_cta: { "url": "/", "label": "Free Consultation" },
				footer_links: [
					{
						"label": "Company",
						"link_list": [
							{
								"link": { "url": "/", "label": "Global location" }
							},
							{
								"link": { "url": "/", "label": "Missions" }
							},
							{
								"link": { "url": "/", "label": "Careers" }
							},
							{
								"link": { "url": "/", "label": "Investors" }
							},
							{
								"link": { "url": "/", "label": "News rooms" }
							}
						]
					},
					{
						"label": "Impact",
						"link_list": [
							{
								"link": { "url": "/", "label": "Creator awards" }
							},
							{
								"link": { "url": "/", "label": "Creative ideas" }
							},
							{
								"link": {
									"url": "/",
									"label": "Refuge initiatives"
								}
							},
							{
								"link": { "url": "/", "label": "Residents" }
							}
						]
					},
					{
						"label": "Partnership",
						"link_list": [
							{
								"link": { "url": "/", "label": "Brokers" }
							},
							{
								"link": { "url": "/", "label": "Impact coffee" }
							},
							{
								"link": { "url": "/", "label": "Table talk" }
							},
							{
								"link": { "url": "/", "label": "Push door" }
							}
						]
					}
				],
				company_description: "<p>Lorem ipsum dolor sit amet, consectetur adipiscing elit. In blandit tincidunt id turpis est platea sed.</p>"
			}
		});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
		}
	};
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$5, safe_not_equal, {});
	}
}

export default Component$6;
