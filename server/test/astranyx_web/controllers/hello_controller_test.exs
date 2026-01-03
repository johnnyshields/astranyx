defmodule AstranyxWeb.HelloControllerTest do
  use AstranyxWeb.ConnCase, async: false

  describe "home/2" do
    test "returns 200 status", %{conn: conn} do
      conn = get(conn, "/")
      assert conn.status == 200
    end

    test "returns HTML content type", %{conn: conn} do
      conn = get(conn, "/")
      assert get_resp_header(conn, "content-type") == ["text/html; charset=utf-8"]
    end

    test "returns HTML with Astranyx Server title", %{conn: conn} do
      conn = get(conn, "/")
      assert conn.resp_body =~ "<title>Astranyx Server</title>"
    end

    test "returns HTML with heading", %{conn: conn} do
      conn = get(conn, "/")
      assert conn.resp_body =~ "<h1>Astranyx Server</h1>"
    end

    test "includes DOCTYPE declaration", %{conn: conn} do
      conn = get(conn, "/")
      assert conn.resp_body =~ "<!DOCTYPE html>"
    end

    test "includes CSS styling", %{conn: conn} do
      conn = get(conn, "/")
      assert conn.resp_body =~ "<style>"
      assert conn.resp_body =~ "background: #1a1a2e"
    end
  end
end
