/**
 * Mensagens SMTP tem o seguinte formato:
 * 
 * <pre>
 *   resposta de uma linha s�:
 *    nnn [SP] lalalal [CR] [LF]
 *   resposta de v�rias linhas:
 *    nnn [-] lalalalal [CR] [LF]
 *    nnn [-] lalalalal [CR] [LF]
 *    ...
 *    nnn [SP] lalalalal [CR] [LF]
 *  </pre>
 */
