# -*- coding: utf-8 -*-
"""
Calculadora Criptográfica (Streamlit)
Autor: Juan Diego Chaparro García

Instalación:   pip install streamlit pandas
Ejecución:     streamlit run calculadora_cripto.py
"""
import base64
import hashlib
import secrets

import pandas as pd
import streamlit as st

st.set_page_config(page_title="Calculadora Criptográfica",layout="wide")

ALF27 = "ABCDEFGHIJKLMNÑOPQRSTUVWXYZ"
ALF26 = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

# =====================================================================
# UTILIDADES GENERALES
# =====================================================================

def explicacion(texto):
    st.info(texto)


def tabla(filas, columnas):
    st.dataframe(pd.DataFrame(filas, columns=columnas).astype(str), hide_index=True)


def entero(etiqueta, valor, clave, minimo=None):
    """Entrada de enteros de cualquier tamaño (útil para RSA y Diffie-Hellman)."""
    s = st.text_input(etiqueta, str(valor), key=clave)
    try:
        n = int(s.strip())
    except ValueError:
        st.error(f"«{etiqueta}» debe ser un número entero.")
        st.stop()
    if minimo is not None and n < minimo:
        st.error(f"«{etiqueta}» debe ser mayor o igual a {minimo}.")
        st.stop()
    return n


def normalizar(texto, alf):
    t = texto.upper()
    for a, b in {"Á": "A", "É": "E", "Í": "I", "Ó": "O", "Ú": "U", "Ü": "U",
                 "À": "A", "È": "E", "Ì": "I", "Ò": "O", "Ù": "U"}.items():
        t = t.replace(a, b)
    if alf == ALF26:
        t = t.replace("Ñ", "N")
    return t


def elegir_alfabeto(clave):
    op = st.radio("Alfabeto", ["Español – 27 letras (con Ñ)", "Inglés – 26 letras"],
                  horizontal=True, key=clave)
    return ALF27 if op.startswith("Español") else ALF26


def elegir_modo(clave, opciones=("Cifrar", "Descifrar")):
    return st.radio("Operación", list(opciones), horizontal=True, key=clave)


def mcd(a, b):
    while b:
        a, b = b, a % b
    return abs(a)


def euclides_pasos(a, b):
    filas = []
    while b != 0:
        q, r = divmod(a, b)
        filas.append((a, b, q, r, f"{a} = {b}·{q} + {r}"))
        a, b = b, r
    return abs(a), filas


def aee(a, n):
    """Algoritmo Extendido de Euclides con tabla i, yᵢ, gᵢ, uᵢ, vᵢ.
    Se cumple en cada fila: gᵢ = n·uᵢ + a·vᵢ."""
    a %= n
    g, u, v, y = [n, a], [1, 0], [0, 1], ["—", "—"]
    i = 1
    while g[i] != 0:
        yi = g[i - 1] // g[i]
        g.append(g[i - 1] - yi * g[i])
        u.append(u[i - 1] - yi * u[i])
        v.append(v[i - 1] - yi * v[i])
        y.append(yi)
        i += 1
    filas = [(k, y[k], g[k], u[k], v[k]) for k in range(len(g))]
    rondas = len(g) - 2
    d = g[-2]
    inv = v[-2] % n if d == 1 else None
    return inv, d, filas, rondas


def es_primo(n):
    """Test de Miller-Rabin (determinista para los tamaños usados en clase)."""
    if n < 2:
        return False
    bases = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    for p in bases:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in bases:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def exp_rapida(base, exp, mod):
    """Exponenciación rápida (cuadrado y multiplica), con registro de pasos."""
    filas = []
    resultado = 1 % mod
    b = base % mod
    e, paso = exp, 0
    while e > 0:
        bit = e & 1
        antes = resultado
        if bit:
            resultado = (resultado * b) % mod
        filas.append((paso, bit, f"{base}^{2 ** paso}", b,
                      f"{antes}·{b} mod {mod} = {resultado}" if bit else f"se mantiene {resultado}"))
        b = (b * b) % mod
        e >>= 1
        paso += 1
    return resultado, filas


# =====================================================================
# 1. OPERACIONES MATEMÁTICAS MODULARES
# =====================================================================

def op_modulo():
    c1, c2 = st.columns(2)
    with c1:
        a = entero("Número a", 27, "m_a")
    with c2:
        n = entero("Módulo n", 5, "m_n", 1)
    b = a % n
    q = (a - b) // n
    st.success(f"**{a} mod {n} = {b}**")
    st.write(f"Verificación: {a} = {n} × {q} + {b}")


def op_inv_aditivo():
    c1, c2 = st.columns(2)
    with c1:
        a = entero("Número a", 7, "ia_a")
    with c2:
        n = entero("Módulo n", 27, "ia_n", 1)
    inv = (-a) % n
    st.success(f"**Inverso aditivo de {a} en mod {n} = {inv}**")
    st.write(f"Cálculo: {n} − ({a} mod {n}) = {n} − {a % n} → {inv} (reducido mod {n})")
    st.write(f"Verificación: ({a} + {inv}) mod {n} = {(a + inv) % n}")


def op_inv_xor():
    c1, c2 = st.columns(2)
    with c1:
        a = entero("Número a (decimal)", 13, "x_a", 0)
    with c2:
        k = entero("Clave k (decimal)", 7, "x_k", 0)
    ancho = max(a.bit_length(), k.bit_length(), 1)
    c = a ^ k
    fb = lambda x: format(x, f"0{ancho}b")
    st.success(f"**Cifrado XOR aplicado**: Al aplicar la clave {k} al número {a}, obtenemos el valor cifrado **{c}**.")
    tabla([
        ("a", a, fb(a)),
        ("k (clave)", k, fb(k)),
        ("c = a ⊕ k (cifrar)", c, fb(c)),
        ("c ⊕ k (descifrar, recupera a)", c ^ k, fb(c ^ k)),
        ("a ⊕ a (inverso de a)", a ^ a, fb(a ^ a)),
    ], ["Operación", "Decimal", "Binario"])


def op_mcd():
    c1, c2 = st.columns(2)
    with c1:
        a = entero("Número a", 15, "mcd_a", 1)
    with c2:
        n = entero("Módulo n", 26, "mcd_n", 1)
    d, filas = euclides_pasos(n, a)
    tabla(filas, ["Dividendo", "Divisor", "Cociente", "Residuo", "Expresión"])
    st.success(f"**MCD({a}, {n}) = {d}**")
    if d == 1:
        st.write(f"✅ Como el MCD es 1, {a} y {n} son coprimos: **sí existe** el inverso multiplicativo de {a} en mod {n}.")
    else:
        st.write(f"❌ Como el MCD es {d} ≠ 1, **no existe** el inverso multiplicativo de {a} en mod {n}.")


def op_inv_tradicional():
    c1, c2 = st.columns(2)
    with c1:
        a = entero("Número a", 7, "it_a", 1)
    with c2:
        n = entero("Módulo n", 26, "it_n", 2)
    ar = a % n
    if mcd(ar, n) != 1:
        st.error(f"MCD({a}, {n}) = {mcd(ar, n)} ≠ 1 → no existe inverso multiplicativo.")
        return
    if ar > 100000:
        st.warning("El número es muy grande para el método tradicional; usa el AEE (opción 1.6).")
        return
    st.write(f"Se busca k tal que (k·{n} + 1) sea divisible entre {ar}; entonces a⁻¹ = (k·{n} + 1) / {ar}.")
    filas, inv = [], None
    for k in range(ar):
        num = k * n + 1
        divisible = num % ar == 0
        filas.append((k, f"{k}·{n} + 1", num, "Sí" if divisible else "No", num // ar if divisible else "—"))
        if divisible:
            inv = num // ar
            break
    tabla(filas, ["k", "Expresión", "Valor", f"¿Divisible entre {ar}?", "Cociente"])
    st.success(f"**Inverso multiplicativo de {a} en mod {n} = {inv}**")
    st.write(f"Verificación: {a} × {inv} mod {n} = {(a * inv) % n}")


def op_aee():
    c1, c2 = st.columns(2)
    with c1:
        a = entero("Número a", 7, "aee_a", 1)
    with c2:
        n = entero("Módulo n", 26, "aee_n", 2)
    inv, d, filas, rondas = aee(a, n)
    tabla(filas, ["i", "yᵢ", "gᵢ", "uᵢ", "vᵢ"])
    st.caption("Reglas: yᵢ₊₁ = ⌊gᵢ₋₁ / gᵢ⌋ · gᵢ₊₁ = gᵢ₋₁ − yᵢ₊₁·gᵢ · uᵢ₊₁ = uᵢ₋₁ − yᵢ₊₁·uᵢ · "
               "vᵢ₊₁ = vᵢ₋₁ − yᵢ₊₁·vᵢ. Se detiene cuando gᵢ = 0.")
    st.write(f"**Número de rondas (divisiones realizadas): {rondas}**")
    if inv is None:
        st.error(f"MCD({a}, {n}) = {d} ≠ 1 → no existe inverso multiplicativo.")
    else:
        v = filas[-2][4]
        st.success(f"**Inverso multiplicativo de {a} en mod {n} = {inv}**")
        if v < 0:
            st.write(f"El último vᵢ fue {v} (negativo), se ajusta: {v} + {n} = {inv}")
        st.write(f"Verificación: {a} × {inv} mod {n} = {(a * inv) % n}")


# =====================================================================
# 2. CRIPTOGRAFÍA CLÁSICA
# =====================================================================

def cifrado_desplazamiento(texto, alf, desplazamientos, descifrar=False):
    m = len(alf)
    texto = normalizar(texto, alf)
    salida, filas, j = [], [], 0
    for ch in texto:
        if ch in alf:
            k = desplazamientos[j % len(desplazamientos)]
            x = alf.index(ch)
            y = (x - k) % m if descifrar else (x + k) % m
            signo = "−" if descifrar else "+"
            filas.append((ch, x, k, f"({x} {signo} {k}) mod {m}", y, alf[y]))
            salida.append(alf[y])
            j += 1
        else:
            salida.append(ch)
    return "".join(salida), filas


def cla_mod27():
    alf = ALF27
    modo = elegir_modo("m27_modo")
    texto = st.text_area("Texto", "HOLA MUNDO", key="m27_txt")
    clave = st.text_input("Clave (un número o una palabra)", "CLAVE", key="m27_k").strip()
    if not clave:
        st.warning("Escribe una clave.")
        return
    if clave.lstrip("-").isdigit():
        desp = [int(clave)]
    else:
        desp = [alf.index(c) for c in normalizar(clave, alf) if c in alf]
        if not desp:
            st.error("La clave no contiene letras válidas.")
            return
        st.caption("Valores de la clave: " + ", ".join(f"{c}={alf.index(c)}" for c in normalizar(clave, alf) if c in alf))
    res, filas = cifrado_desplazamiento(texto, alf, desp, modo == "Descifrar")
    st.success(f"**Resultado:** {res}")
    with st.expander("Ver tabla de cálculo"):
        tabla(filas, ["Letra", "Valor", "Clave", "Operación", "Resultado", "Letra final"])


def cla_cesar():
    alf = elegir_alfabeto("ces_alf")
    modo = elegir_modo("ces_modo")
    texto = st.text_area("Texto", "HOLA MUNDO", key="ces_txt")
    k = st.number_input("Desplazamiento", 0, len(alf) - 1, 3, key="ces_k")
    res, filas = cifrado_desplazamiento(texto, alf, [int(k)], modo == "Descifrar")
    st.success(f"**Resultado:** {res}")
    st.caption(f"Alfabeto claro:   {alf}\n\nAlfabeto cifrado: {alf[int(k):] + alf[:int(k)]}")
    with st.expander("Ver tabla de cálculo"):
        tabla(filas, ["Letra", "Valor", "k", "Operación", "Resultado", "Letra final"])


def cla_vernam():
    modo = elegir_modo("ver_modo")
    clave = st.text_input("Clave", "SECRETO", key="ver_k")
    if not clave:
        st.warning("Escribe una clave.")
        return
    kb = clave.encode("utf-8")
    if modo == "Cifrar":
        texto = st.text_area("Mensaje", "HOLA", key="ver_txt")
        mb = texto.encode("utf-8")
        if len(kb) < len(mb):
            st.warning("La clave es más corta que el mensaje y se repetirá. En un Vernam ideal "
                       "(one-time pad) la clave debe ser tan larga como el mensaje y usarse una sola vez.")
        cb = bytes(m ^ kb[i % len(kb)] for i, m in enumerate(mb))
        st.success(f"**Criptograma (hexadecimal):** {cb.hex(' ').upper()}")
        filas = [(i + 1, chr(m) if 32 <= m < 127 else "·", format(m, "08b"),
                  chr(kb[i % len(kb)]) if 32 <= kb[i % len(kb)] < 127 else "·",
                  format(kb[i % len(kb)], "08b"), format(c, "08b"), format(c, "02X"))
                 for i, (m, c) in enumerate(zip(mb, cb))]
        with st.expander("Ver tabla XOR bit a bit"):
            tabla(filas, ["#", "M", "M (bin)", "K", "K (bin)", "M ⊕ K", "Hex"])
    else:
        hx = st.text_area("Criptograma en hexadecimal", "1B 0A 0F 13", key="ver_hex")
        try:
            cb = bytes.fromhex(hx.replace(" ", ""))
        except ValueError:
            st.error("El criptograma debe estar en hexadecimal válido (ej.: 1B 0A 0F 04).")
            return
        mb = bytes(c ^ kb[i % len(kb)] for i, c in enumerate(cb))
        st.success(f"**Mensaje descifrado:** {mb.decode('utf-8', errors='replace')}")


def cla_atbash():
    alf = elegir_alfabeto("atb_alf")
    texto = st.text_area("Texto (Atbash cifra y descifra igual)", "HOLA MUNDO", key="atb_txt")
    inv = alf[::-1]
    t = normalizar(texto, alf)
    res = "".join(inv[alf.index(c)] if c in alf else c for c in t)
    st.success(f"**Resultado:** {res}")
    st.dataframe(pd.DataFrame([list(alf), list(inv)], index=["Claro", "Cifrado"]))


def orden_clave(clave):
    return sorted(range(len(clave)), key=lambda i: (clave[i], i))


def cla_transposicion():
    modo = elegir_modo("tr_modo")
    clave = normalizar(st.text_input("Palabra clave (define el número y orden de columnas)", "CLAVE", key="tr_k").strip(), ALF27)
    texto = st.text_area("Texto", "ATAQUE AL AMANECER", key="tr_txt")
    quitar = st.checkbox("Eliminar espacios", True, key="tr_esp")
    if len(clave) < 2:
        st.warning("La clave debe tener al menos 2 caracteres.")
        return
    t = normalizar(texto, ALF27)
    if quitar:
        t = t.replace(" ", "")
    n = len(clave)
    orden = orden_clave(clave)
    rango = [0] * n
    for pos, c in enumerate(orden):
        rango[c] = pos + 1

    if modo == "Cifrar":
        relleno = st.text_input("Carácter de relleno", "X", max_chars=1, key="tr_rel") or "X"
        if len(t) % n:
            t += relleno * (n - len(t) % n)
        filas = [t[i:i + n] for i in range(0, len(t), n)]
        res = "".join("".join(f[c] for f in filas) for c in orden)
    else:
        if len(t) % n:
            st.error(f"La longitud del criptograma ({len(t)}) debe ser múltiplo del número de columnas ({n}).")
            return
        r = len(t) // n
        cols, pos = [None] * n, 0
        for c in orden:
            cols[c] = t[pos:pos + r]
            pos += r
        filas = ["".join(cols[c][i] for c in range(n)) for i in range(r)]
        res = "".join(filas)

    st.success(f"**Resultado:** {res}")
    columnas = [f"{clave[i]} ({i + 1})" for i in range(n)]
    matriz = [[str(x) for x in rango]] + [list(f) for f in filas]
    st.write("Matriz (la primera fila indica el orden de lectura de cada columna):")
    st.dataframe(pd.DataFrame(matriz, columns=columnas, index=["Orden"] + [f"Fila {i + 1}" for i in range(len(filas))]))


def cla_afin():
    alf = elegir_alfabeto("af_alf")
    m = len(alf)
    modo = elegir_modo("af_modo")
    texto = st.text_area("Texto", "HOLA MUNDO", key="af_txt")
    c1, c2 = st.columns(2)
    with c1:
        a = st.number_input("a (multiplicador, coprimo con el módulo)", 1, m - 1, 5, key="af_a")
    with c2:
        b = st.number_input("b (desplazamiento)", 0, m - 1, 8, key="af_b")
    a, b = int(a), int(b)
    if mcd(a, m) != 1:
        st.error(f"MCD({a}, {m}) ≠ 1: la clave a no es válida porque no tiene inverso en mod {m}.")
        return
    a_inv = aee(a, m)[0]
    t = normalizar(texto, alf)
    salida, filas = [], []
    for ch in t:
        if ch in alf:
            x = alf.index(ch)
            if modo == "Cifrar":
                y = (a * x + b) % m
                op = f"({a}·{x} + {b}) mod {m}"
            else:
                y = (a_inv * (x - b)) % m
                op = f"{a_inv}·({x} − {b}) mod {m}"
            filas.append((ch, x, op, y, alf[y]))
            salida.append(alf[y])
        else:
            salida.append(ch)
    st.caption(f"Cifrar: C = (a·M + b) mod {m} · Descifrar: M = a⁻¹·(C − b) mod {m} · a⁻¹ = {a_inv}")
    st.success(f"**Resultado:** {''.join(salida)}")
    with st.expander("Ver tabla de cálculo"):
        tabla(filas, ["Letra", "Valor", "Operación", "Resultado", "Letra final"])


def cla_sustitucion():
    alf = elegir_alfabeto("sus_alf")
    modo = elegir_modo("sus_modo")
    forma = st.radio("¿Cómo generar el alfabeto cifrado?", ["A partir de palabra clave", "Escribir alfabeto completo"],
                     horizontal=True, key="sus_forma")
    if forma == "A partir de palabra clave":
        kw = normalizar(st.text_input("Palabra clave", "CRIPTOGRAFIA", key="sus_kw"), alf)
        sust = []
        for c in kw + alf:
            if c in alf and c not in sust:
                sust.append(c)
        sust = "".join(sust)
    else:
        sust = normalizar(st.text_input(f"Alfabeto cifrado ({len(alf)} letras, sin repetir)",
                                        alf[::-1], key="sus_full").replace(" ", ""), alf)
        if sorted(sust) != sorted(alf):
            st.error(f"El alfabeto cifrado debe contener exactamente las {len(alf)} letras sin repetir.")
            return
    texto = st.text_area("Texto", "HOLA MUNDO", key="sus_txt")
    origen, destino = (alf, sust) if modo == "Cifrar" else (sust, alf)
    t = normalizar(texto, alf)
    res = "".join(destino[origen.index(c)] if c in origen else c for c in t)
    st.success(f"**Resultado:** {res}")
    st.dataframe(pd.DataFrame([list(alf), list(sust)], index=["Claro", "Cifrado"]))


# =====================================================================
# 3. CRIPTOGRAFÍA MODERNA
# =====================================================================

def mod_diffie_hellman():
    c1, c2 = st.columns(2)
    with c1:
        p = entero("Primo p (público)", 23, "dh_p", 3)
        a = entero("Secreto de Alice (a)", 6, "dh_a", 1)
    with c2:
        g = entero("Generador g (público)", 5, "dh_g", 2)
        b = entero("Secreto de Bob (b)", 15, "dh_b", 1)
    if not es_primo(p):
        st.warning(f"{p} no es primo; Diffie-Hellman requiere un módulo primo.")
    A = pow(g, a, p)
    B = pow(g, b, p)
    kA = pow(B, a, p)
    kB = pow(A, b, p)
    tabla([
        ("Alice calcula A = gᵃ mod p", f"{g}^{a} mod {p}", A),
        ("Bob calcula B = gᵇ mod p", f"{g}^{b} mod {p}", B),
        ("Alice obtiene K = Bᵃ mod p", f"{B}^{a} mod {p}", kA),
        ("Bob obtiene K = Aᵇ mod p", f"{A}^{b} mod {p}", kB),
    ], ["Paso", "Operación", "Resultado"])
    if kA == kB:
        st.success(f"**Clave secreta compartida K = {kA}**")
    st.caption("Se intercambian públicamente A y B; los secretos a y b nunca viajan por el canal.")


def mod_rsa():
    c1, c2, c3 = st.columns(3)
    with c1:
        p = entero("Primo p", 61, "rsa_p", 2)
    with c2:
        q = entero("Primo q", 53, "rsa_q", 2)
    with c3:
        e = entero("Exponente público e", 17, "rsa_e", 2)
    for nombre, val in (("p", p), ("q", q)):
        if not es_primo(val):
            st.error(f"{nombre} = {val} no es primo.")
            return
    if p == q:
        st.error("p y q deben ser distintos.")
        return
    n = p * q
    phi = (p - 1) * (q - 1)
    if mcd(e, phi) != 1:
        st.error(f"MCD(e, φ(n)) = MCD({e}, {phi}) = {mcd(e, phi)} ≠ 1 → elige otro e.")
        return
    d, _, filas, rondas = aee(e, phi)
    tabla([
        ("n = p·q", f"{p}·{q}", n),
        ("φ(n) = (p−1)(q−1)", f"{p - 1}·{q - 1}", phi),
        ("MCD(e, φ(n))", f"MCD({e}, {phi})", 1),
        ("d = e⁻¹ mod φ(n)", f"{e}⁻¹ mod {phi}", d),
    ], ["Concepto", "Operación", "Valor"])
    st.success(f"**Clave pública (e, n) = ({e}, {n}) · Clave privada (d, n) = ({d}, {n})**")
    with st.expander(f"Ver cálculo de d con AEE ({rondas} rondas)"):
        tabla(filas, ["i", "yᵢ", "gᵢ", "uᵢ", "vᵢ"])

    st.markdown("#### Cifrar / descifrar")
    modo = elegir_modo("rsa_modo")
    tipo = st.radio("Tipo de mensaje", ["Número", "Texto (carácter por carácter, código ASCII)"],
                    horizontal=True, key="rsa_tipo")
    if tipo == "Número":
        etiqueta = "Mensaje M (número < n)" if modo == "Cifrar" else "Criptograma C (número < n)"
        x = entero(etiqueta, 65, "rsa_x", 0)
        if x >= n:
            st.error(f"El valor debe ser menor que n = {n}.")
            return
        if modo == "Cifrar":
            st.success(f"**C = M^e mod n = {x}^{e} mod {n} = {pow(x, e, n)}**")
        else:
            st.success(f"**M = C^d mod n = {x}^{d} mod {n} = {pow(x, d, n)}**")
    else:
        if modo == "Cifrar":
            texto = st.text_input("Texto", "HOLA", key="rsa_txt")
            codigos = [ord(c) for c in texto]
            if codigos and max(codigos) >= n:
                st.error(f"n = {n} es muy pequeño para estos caracteres; usa primos más grandes.")
                return
            cif = [pow(m, e, n) for m in codigos]
            st.success(f"**Criptograma:** {' '.join(map(str, cif))}")
            tabla([(c, m, f"{m}^{e} mod {n}", x) for c, m, x in zip(texto, codigos, cif)],
                  ["Carácter", "Código", "Operación", "Cifrado"])
        else:
            s = st.text_input("Números cifrados separados por espacio", "", key="rsa_nums")
            try:
                nums = [int(t) for t in s.replace(",", " ").split()]
                st.success(f"**Texto descifrado:** {''.join(chr(pow(c, d, n)) for c in nums)}")
            except (ValueError, OverflowError):
                st.error("Ingresa solo números enteros válidos separados por espacio.")


def mod_exp_rapida():
    c1, c2, c3 = st.columns(3)
    with c1:
        a = entero("Base a", 7, "er_a", 0)
    with c2:
        e = entero("Exponente e", 13, "er_e", 0)
    with c3:
        n = entero("Módulo n", 11, "er_n", 1)
    res, filas = exp_rapida(a, e, n)
    st.write(f"Exponente en binario: **{bin(e)[2:]}** (se recorre de derecha a izquierda)")
    tabla(filas, ["Paso", "Bit", "Potencia", "Valor mod n", "Acumulado"])
    st.success(f"**{a}^{e} mod {n} = {res}**")
    st.caption(f"Comprobación con pow(): {pow(a, e, n)}")


# =====================================================================
# 4. ALGORITMOS HASH
# =====================================================================

def seccion_hash(nombre, funcion, clave):
    texto = st.text_area("Texto de entrada", "Hola mundo", key=f"{clave}_txt")
    archivo = st.file_uploader("…o sube un archivo (opcional)", key=f"{clave}_file")
    datos = archivo.getvalue() if archivo else texto.encode("utf-8")
    h = funcion(datos).hexdigest()
    st.success(f"**{nombre}:**")
    st.code(h, language=None)
    st.write(f"Longitud: {len(h)} caracteres hexadecimales = {len(h) * 4} bits")
    comparar = st.text_input("Compara con otro texto (efecto avalancha)", "Hola mundo.", key=f"{clave}_cmp")
    if comparar:
        h2 = funcion(comparar.encode("utf-8")).hexdigest()
        st.code(h2, language=None)
        iguales = sum(x == y for x, y in zip(h, h2))
        st.caption(f"Caracteres coincidentes en la misma posición: {iguales} de {len(h)}. "
                   "Un cambio mínimo en la entrada produce un hash completamente distinto.")


def hash_md5():
    seccion_hash("MD5", hashlib.md5, "md5")


def hash_sha256():
    seccion_hash("SHA-256", hashlib.sha256, "s256")


def hash_sha512():
    seccion_hash("SHA-512", hashlib.sha512, "s512")


# =====================================================================
# 5. CODIFICACIÓN
# =====================================================================

def tabla_caracteres(texto):
    filas = []
    for c in texto:
        for byte in c.encode("utf-8"):
            filas.append((c, byte, format(byte, "02X"), format(byte, "08b")))
    with st.expander("Ver tabla por carácter"):
        tabla(filas, ["Carácter", "Decimal", "Hex", "Binario"])


def cod_ascii():
    modo = elegir_modo("asc_modo", ("Codificar", "Decodificar"))
    if modo == "Codificar":
        t = st.text_area("Texto", "Hola", key="asc_txt")
        st.success(f"**Códigos ASCII:** {' '.join(str(ord(c)) for c in t)}")
        if any(ord(c) > 127 for c in t):
            st.warning("Hay caracteres fuera del ASCII estándar (0–127); se muestra su código Unicode.")
        tabla_caracteres(t)
    else:
        s = st.text_area("Códigos decimales separados por espacio", "72 111 108 97", key="asc_cod")
        try:
            st.success(f"**Texto:** {''.join(chr(int(x)) for x in s.replace(',', ' ').split())}")
        except (ValueError, OverflowError):
            st.error("Ingresa solo números enteros separados por espacio.")


def cod_hex():
    modo = elegir_modo("hex_modo", ("Codificar", "Decodificar"))
    if modo == "Codificar":
        t = st.text_area("Texto", "Hola", key="hex_txt")
        st.success(f"**Hexadecimal:** {t.encode('utf-8').hex(' ').upper()}")
        tabla_caracteres(t)
    else:
        s = st.text_area("Hexadecimal", "48 6F 6C 61", key="hex_cod")
        try:
            st.success(f"**Texto:** {bytes.fromhex(s.replace(' ', '')).decode('utf-8')}")
        except (ValueError, UnicodeDecodeError):
            st.error("Hexadecimal no válido.")


def cod_binario():
    modo = elegir_modo("bin_modo", ("Codificar", "Decodificar"))
    if modo == "Codificar":
        t = st.text_area("Texto", "Hola", key="bin_txt")
        st.success(f"**Binario:** {' '.join(format(b, '08b') for b in t.encode('utf-8'))}")
        tabla_caracteres(t)
    else:
        s = st.text_area("Binario (grupos de 8 bits)", "01001000 01101111 01101100 01100001", key="bin_cod")
        bits = s.replace(" ", "").replace("\n", "")
        if len(bits) % 8 or any(c not in "01" for c in bits):
            st.error("El binario debe contener solo 0 y 1, en grupos de 8 bits.")
            return
        try:
            datos = bytes(int(bits[i:i + 8], 2) for i in range(0, len(bits), 8))
            st.success(f"**Texto:** {datos.decode('utf-8')}")
        except UnicodeDecodeError:
            st.error("Los bytes no forman texto UTF-8 válido.")


def cod_base64():
    modo = elegir_modo("b64_modo", ("Codificar", "Decodificar"))
    if modo == "Codificar":
        t = st.text_area("Texto", "Hola mundo", key="b64_txt")
        st.success(f"**Base64:** {base64.b64encode(t.encode('utf-8')).decode()}")
    else:
        s = st.text_area("Base64", "SG9sYSBtdW5kbw==", key="b64_cod")
        try:
            st.success(f"**Texto:** {base64.b64decode(s.strip(), validate=True).decode('utf-8')}")
        except (ValueError, UnicodeDecodeError):
            st.error("Base64 no válido.")


# =====================================================================
# 6. USO DE SALT
# =====================================================================

def seccion_salt(nombre, funcion, clave):
    pwd = st.text_input("Contraseña", "Clave123", key=f"{clave}_pwd")
    c1, c2, c3 = st.columns(3)
    with c1:
        cantidad = st.slider("Número de salts", 1, 10, 3, key=f"{clave}_n")
    with c2:
        largo = st.slider("Longitud del salt (bytes)", 4, 32, 16, key=f"{clave}_l")
    with c3:
        posicion = st.radio("Concatenación", ["salt + contraseña", "contraseña + salt"], key=f"{clave}_pos")

    st.write(f"**{nombre} sin salt:**")
    st.code(funcion(pwd.encode("utf-8")).hexdigest(), language=None)

    if st.button(f"Generar hashes {nombre} con salts diferentes", key=f"{clave}_btn"):
        filas = []
        for i in range(cantidad):
            salt = secrets.token_hex(largo)
            datos = salt + pwd if posicion.startswith("salt") else pwd + salt
            filas.append((i + 1, salt, funcion(datos.encode("utf-8")).hexdigest()))
        st.session_state[f"{clave}_res"] = filas
    if f"{clave}_res" in st.session_state:
        tabla(st.session_state[f"{clave}_res"], ["#", "Salt (hex)", f"Hash {nombre}"])
        st.caption("Misma contraseña, salts distintos → hashes totalmente distintos. "
                   "El salt se guarda junto al hash; no es secreto, pero impide usar tablas precalculadas.")

    with st.expander("Verificar una contraseña con su salt"):
        s = st.text_input("Salt almacenado", key=f"{clave}_vs")
        h = st.text_input("Hash almacenado", key=f"{clave}_vh")
        intento = st.text_input("Contraseña a verificar", key=f"{clave}_vp")
        if s and h and intento:
            datos = s + intento if posicion.startswith("salt") else intento + s
            if funcion(datos.encode("utf-8")).hexdigest() == h.strip().lower():
                st.success("✅ La contraseña es correcta.")
            else:
                st.error("❌ La contraseña no coincide.")


def salt_md5():
    seccion_salt("MD5", hashlib.md5, "smd5")


def salt_sha256():
    seccion_salt("SHA-256", hashlib.sha256, "ss256")


def salt_sha512():
    seccion_salt("SHA-512", hashlib.sha512, "ss512")


# =====================================================================
# ESTRUCTURA DE MENÚS Y EXPLICACIONES
# =====================================================================

MENU = {
    "1. Operaciones matemáticas modulares": {
        "desc": "La aritmética modular trabaja con los residuos de una división: los números «dan la vuelta» al "
                "llegar al módulo n, como las horas de un reloj. Es la base matemática de casi toda la "
                "criptografía, tanto clásica (César, afín) como moderna (RSA, Diffie-Hellman).",
        "sub": {
            "1.1 Módulo de dos números (a mod n = b)": (
                "Calcula el residuo b de dividir a entre n, de modo que a = n·q + b con 0 ≤ b < n. "
                "Sirve para reducir cualquier número al rango 0…n−1.", op_modulo),
            "1.2 Inverso aditivo": (
                "El inverso aditivo de a en mod n es el número que sumado con a da 0 (mod n). "
                "Se usa para «deshacer» sumas, por ejemplo al descifrar César (restar k es sumar su inverso aditivo).",
                op_inv_aditivo),
            "1.3 Inverso de XOR": (
                "XOR (⊕) es la suma bit a bit sin acarreo. Cada número es su propio inverso: a ⊕ a = 0. "
                "Por eso aplicar dos veces la misma clave recupera el original: (a ⊕ k) ⊕ k = a. "
                "Es la operación central del cifrado Vernam y de muchos cifradores modernos.", op_inv_xor),
            "1.4 MCD y existencia de inverso multiplicativo": (
                "Calcula el máximo común divisor con el algoritmo de Euclides (divisiones sucesivas). "
                "Si MCD(a, n) = 1, a y n son coprimos y existe el inverso multiplicativo de a en mod n.", op_mcd),
            "1.5 Inverso multiplicativo – método tradicional": (
                "Busca el número x tal que a·x ≡ 1 (mod n) probando valores de k hasta que (k·n + 1) "
                "sea divisible entre a; entonces x = (k·n + 1)/a. Es sencillo, pero lento para números grandes.",
                op_inv_tradicional),
            "1.6 Inverso multiplicativo – Algoritmo Extendido de Euclides (AEE)": (
                "El AEE calcula el MCD y, a la vez, los coeficientes que permiten escribir 1 = n·u + a·v; "
                "el valor v (mod n) es el inverso. Es eficiente incluso con números enormes, por eso se usa "
                "para calcular la clave privada d en RSA. Se muestra la tabla completa y el número de rondas.", op_aee),
        },
    },
    "2. Criptografía clásica": {
        "desc": "Métodos históricos que operan sobre letras mediante sustitución (cambiar una letra por otra) o "
                "transposición (cambiar el orden de las letras). Hoy son inseguros, pero enseñan los principios "
                "de confusión y difusión en los que se basa la criptografía actual.",
        "sub": {
            "2.1 Cifrado módulo 27": (
                "Asigna a cada letra del alfabeto español un número (A=0 … Ñ=14 … Z=26) y le suma la clave "
                "en módulo 27: C = (M + K) mod 27. La clave puede ser un número o una palabra que se repite "
                "sobre el mensaje. Para descifrar se resta: M = (C − K) mod 27.", cla_mod27),
            "2.2 Cifrado César": (
                "Desplaza cada letra un número fijo de posiciones en el alfabeto (Julio César usaba 3). "
                "Solo hay tantas claves como letras, por lo que se rompe probándolas todas (fuerza bruta).", cla_cesar),
            "2.3 Cifrado Vernam": (
                "Combina cada bit del mensaje con un bit de la clave mediante XOR. Si la clave es aleatoria, "
                "tan larga como el mensaje y se usa una sola vez (one-time pad), el cifrado es perfectamente seguro.",
                cla_vernam),
            "2.4 Cifrado Atbash": (
                "Sustituye cada letra por su «espejo» en el alfabeto: A↔Z, B↔Y, etc. No tiene clave y la misma "
                "operación sirve para cifrar y descifrar. Proviene de textos hebreos antiguos.", cla_atbash),
            "2.5 Transposición columnar simple": (
                "Escribe el mensaje por filas en una matriz con tantas columnas como letras de la clave, y lo lee "
                "por columnas en el orden alfabético de la clave. Las letras no cambian, solo su posición.",
                cla_transposicion),
            "2.6 Cifrado afín": (
                "Generaliza el César con una multiplicación: C = (a·M + b) mod m. La clave a debe ser coprima "
                "con m para que exista su inverso y se pueda descifrar con M = a⁻¹·(C − b) mod m.", cla_afin),
            "2.7 Cifra de sustitución simple": (
                "Cada letra se reemplaza siempre por la misma letra de un alfabeto desordenado (generado con una "
                "palabra clave o escrito completo). Tiene muchísimas claves, pero es vulnerable al análisis de "
                "frecuencias.", cla_sustitucion),
        },
    },
    "3. Criptografía moderna": {
        "desc": "Algoritmos basados en problemas matemáticos difíciles de resolver, como el logaritmo discreto o la "
                "factorización de números grandes. Permiten intercambiar claves y cifrar con clave pública.",
        "sub": {
            "3.1 Diffie-Hellman": (
                "Protocolo que permite a dos personas acordar una clave secreta común a través de un canal "
                "público, sin enviarla nunca. Su seguridad se basa en la dificultad del logaritmo discreto.",
                mod_diffie_hellman),
            "3.2 RSA": (
                "Cifrado de clave pública: se cifra con (e, n) y solo quien tiene la clave privada (d, n) puede "
                "descifrar. Su seguridad se basa en la dificultad de factorizar n = p·q cuando p y q son primos grandes.",
                mod_rsa),
            "3.3 Exponenciación rápida": (
                "Calcula aᵉ mod n de forma eficiente usando la representación binaria del exponente "
                "(elevar al cuadrado y multiplicar). Es indispensable en RSA y Diffie-Hellman, donde los "
                "exponentes tienen cientos de dígitos.", mod_exp_rapida),
        },
    },
    "4. Algoritmos hash": {
        "desc": "Una función hash transforma datos de cualquier tamaño en una «huella digital» de longitud fija. "
                "Es de un solo sentido (no se puede revertir) y un cambio mínimo en la entrada cambia totalmente "
                "la salida. Se usa para verificar integridad, firmas digitales y almacenar contraseñas.",
        "sub": {
            "4.1 MD5": (
                "Produce un hash de 128 bits (32 caracteres hexadecimales). Es rápido pero se considera roto "
                "porque se pueden fabricar colisiones; hoy solo se usa para verificaciones no críticas.", hash_md5),
            "4.2 SHA-256": (
                "De la familia SHA-2, produce 256 bits (64 caracteres hex). Es el estándar actual: se usa en "
                "certificados TLS, firmas digitales y blockchain.", hash_sha256),
            "4.3 SHA-512": (
                "También de la familia SHA-2, produce 512 bits (128 caracteres hex). Ofrece mayor margen de "
                "seguridad y suele ser más rápido que SHA-256 en procesadores de 64 bits.", hash_sha512),
        },
    },
    "5. Codificación": {
        "desc": "Codificar es representar la información en otro formato para almacenarla o transmitirla. "
                "No es cifrado: no usa clave y cualquiera puede decodificarla.",
        "sub": {
            "5.1 ASCII": (
                "Asigna a cada carácter un número entre 0 y 127 (por ejemplo, A = 65). Es la base de la "
                "representación de texto en las computadoras.", cod_ascii),
            "5.2 Hexadecimal": (
                "Representa cada byte con dos dígitos en base 16 (0-9, A-F). Se usa para mostrar datos binarios, "
                "hashes y claves de forma compacta.", cod_hex),
            "5.3 Binario": (
                "Representa cada byte como 8 bits (0 y 1), el lenguaje nativo de la computadora. Permite ver "
                "exactamente qué bits se operan en XOR o Vernam.", cod_binario),
            "5.4 Base64": (
                "Convierte datos binarios en texto usando 64 caracteres imprimibles. Se usa para enviar archivos "
                "por correo, en URLs, JSON y certificados.", cod_base64),
        },
    },
    "6. Uso de SALT": {
        "desc": "Un salt es un valor aleatorio que se une a la contraseña antes de calcular su hash. Así dos "
                "usuarios con la misma contraseña tienen hashes distintos y se neutralizan los ataques con "
                "tablas precalculadas (rainbow tables).",
        "sub": {
            "6.1 Hash de claves con MD5 y salts diferentes": (
                "Genera varios salts aleatorios para una misma contraseña y muestra que cada hash MD5 resultante es "
                "diferente. También permite verificar una contraseña con su salt.", salt_md5),
            "6.2 Hash de claves con SHA-256 y salts diferentes": (
                "Igual que el anterior pero con SHA-256, un algoritmo seguro en la actualidad.", salt_sha256),
            "6.3 Hash de claves con SHA-512 y salts diferentes": (
                "Igual que el anterior pero con SHA-512, que ofrece un hash más largo (512 bits).", salt_sha512),
        },
    },
}

# =====================================================================
# INTERFAZ
# =====================================================================

st.markdown(
    """
    <div style="text-align:center; padding: 0.5rem 0 1rem 0;">
        <h1 style="margin-bottom:0.2rem;"> Calculadora Criptográfica</h1>
        <p style="font-size:1.15rem; margin:0; opacity:0.8;">Juan Diego Chaparro García</p>
    </div>
    """,
    unsafe_allow_html=True,
)
st.divider()

with st.sidebar:
    st.header("Menú principal")
    seccion = st.radio("Sección", list(MENU.keys()), label_visibility="collapsed")
    st.divider()
    st.subheader("Submenú")
    opcion = st.radio("Opción", list(MENU[seccion]["sub"].keys()), label_visibility="collapsed")

st.header(seccion)
explicacion(MENU[seccion]["desc"])
st.subheader(opcion)
desc_sub, funcion = MENU[seccion]["sub"][opcion]
st.markdown(f"*{desc_sub}*")
st.write("")
funcion()